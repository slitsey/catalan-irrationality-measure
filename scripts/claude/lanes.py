"""Shared memory-aware build lanes (Claude, 28 Oct 2026).

One driver admits guarded builds from every agent, so the host stays full but never
runs out of physical memory or commit charge.

    driver:  <python> -I scripts/claude/lanes.py drive
    agent:   <python> -I scripts/claude/lanes.py submit <Module.Name> [budgetGB]
             (blocks until the build ends; prints the receipt JSON; exit code = rc)

    any job: <python> -I scripts/claude/lanes.py run <label> <GB> -- <command ...>

Admission (manage-compute-campaigns skill): the first queued job, in priority order, that
fits starts when free + own live workers - floor(3) - margin(1) covers the remaining forecast
peaks of every running job plus the new one, for both working set and commit charge.
Forecasts are per-class peaks learned from receipts. A build whose stale frontier is more
than itself is refused. Near the floor the driver sheds its youngest owned job tree (by PID)
and requeues it once.
"""
import ctypes as C, json, os, subprocess, sys, time, uuid
from pathlib import Path

ROOT = Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
WORK = ROOT / 'work/catalan-uniform'
PY = Path(r'C:\Users\seanl\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
LANES = ROOT / 'work/tools/lanes'
Q, RUN, DONE, OUTD = LANES / 'queue', LANES / 'running', LANES / 'done', LANES / 'out'
for d in (Q, RUN, DONE, OUTD):
    d.mkdir(parents=True, exist_ok=True)
MAXLANES, RAMP, STARVE = 6, 10, 300
FLOOR, MARGIN = 3.0, 1.0   # manage-compute-campaigns: system floor and operating margin (GB)
THREADS = '4'   # lanes run in parallel, so each lean needs few worker threads (default = 22 cores)
# 28 Oct 10:46: the watchdog killed a tube cell at < 3 GB free commit with 2 lanes: heavy
# modules peak near 6 GB commit (3.5 GB working set) + 1 GB for lake. Admission now uses a
# per-class peak learned from receipts (class = module name minus its last component):
# commit ~ 1.75 x peak working set + 1 GB, default 7 GB until measured. Every running job is
# assumed able to grow by half its class peak.
LEARN = LANES / 'peaks.json'
def cls(t): return t.rsplit('.', 1)[0]
def peaks():
    try: return json.loads(LEARN.read_text(encoding='utf-8'))
    except Exception: return {}
def est(t):
    ws = peaks().get(cls(t))
    return (1.75 * ws + 1.0, ws) if ws else (7.0, 3.5)
def learn(t, out):
    import re
    m = re.search(r'"lean_process_peak_working_sets_bytes": \{([^}]*)\}', out)
    if not m: return
    vals = [int(v) for v in re.findall(r': (\d+)', m.group(1))]
    if not vals: return
    pk = peaks(); c = cls(t)
    pk[c] = max(pk.get(c, 0), max(vals) / 2**30)
    LEARN.write_text(json.dumps(pk, indent=1), encoding='utf-8')
# Measured 28 Oct 09:50: one build holds about 3.6 GB of commit (lean 2.5 + lake 1.0) at
# 1.7 GB working set. Reserves above were sized from a wrong 6 GB/job reading.
# RAMP was 45 s; with YOUNG accounting it only throttled throughput to one start per 45 s.
# 28 Oct 09:31: commit fell to 6 GB with 8 lanes because jobs admitted <2 min earlier had
# not reached peak. Admission now also subtracts the budget of every job younger than
# YOUNG seconds, refuses a target that is already running, and honours LANES/PAUSE.


class MS(C.Structure):
    _fields_ = [('len', C.c_ulong), ('load', C.c_ulong)] + [(n, C.c_ulonglong) for n in
               ('tphys', 'aphys', 'tpage', 'apage', 'tvirt', 'avirt', 'aext')]


def mem():
    m = MS(); m.len = C.sizeof(MS)
    C.windll.kernel32.GlobalMemoryStatusEx(C.byref(m))
    return m.aphys / 2**30, m.apage / 2**30   # free physical, free commit (GB)


from ctypes import wintypes as W
class PE(C.Structure):
    _fields_ = [('size', W.DWORD), ('usage', W.DWORD), ('pid', W.DWORD), ('heap', C.c_size_t),
                ('module', W.DWORD), ('threads', W.DWORD), ('parent', W.DWORD),
                ('prio', W.LONG), ('flags', W.DWORD), ('exe', W.WCHAR * 260)]
class PMC(C.Structure):
    _fields_ = [('cb', W.DWORD), ('faults', W.DWORD)] + [(n, C.c_size_t) for n in
               ('peak', 'ws', 'qppp', 'qpp', 'qpnpp', 'qnpp', 'pagefile', 'peakpf', 'private')]
K32, PSAPI = C.WinDLL('kernel32'), C.WinDLL('psapi')
K32.CreateToolhelp32Snapshot.restype = W.HANDLE
K32.OpenProcess.restype = W.HANDLE


def tree_usage(roots):
    """(working set GB, commit GB) of each root's descendant tree, keyed by root pid."""
    h = K32.CreateToolhelp32Snapshot(2, 0); e = PE(); e.size = C.sizeof(e); kids = {}
    ok = K32.Process32FirstW(h, C.byref(e))
    while ok:
        kids.setdefault(e.parent, []).append(e.pid); ok = K32.Process32NextW(h, C.byref(e))
    K32.CloseHandle(h)
    out = {}
    for r in roots:
        ws = pv = 0.0; stack = [r]; seen = set()
        while stack:
            pid = stack.pop()
            if pid in seen: continue
            seen.add(pid); stack += kids.get(pid, [])
            ph = K32.OpenProcess(0x1000 | 0x0400, False, pid)
            if ph:
                m = PMC(); m.cb = C.sizeof(m)
                if PSAPI.GetProcessMemoryInfo(ph, C.byref(m), m.cb):
                    ws += m.ws / 2**30; pv += m.private / 2**30
                K32.CloseHandle(ph)
        out[r] = (ws, pv)
    return out


def registry_refusal(target):
    """CANONICAL.md enforcement: a NEW (untracked) module must sit under a registered prefix
    and must not be a scratch/pilot/demo file. Tracked modules always build."""
    rel = target.replace('.', '/') + '.lean'
    tracked = subprocess.run(['git', 'ls-files', '--error-unmatch', rel], cwd=WORK,
                             capture_output=True).returncode == 0
    if tracked:
        return None
    last = target.rsplit('.', 1)[-1].lower()
    if any(last.startswith(w) for w in ('scratch', 'pilot', 'demo')):
        return f'new module {target} is a scratch/pilot/demo file; put experiments in scratch/ (CANONICAL.md rule 4)'
    try:
        allow = [l.strip() for l in (LANES / 'allow.txt').read_text(encoding='utf-8').splitlines()
                 if l.strip() and not l.startswith('#')]
    except OSError:
        return None
    if not any(target == a or target.startswith(a + '.') for a in allow):
        return f'new module {target} is outside the registered canonical prefixes (CANONICAL.md); extend the canonical module or ask the coordinator to register a directory'
    return None


def stale_count(target):
    r = subprocess.run([str(PY), '-I', 'scripts/claude/run_guarded.py', target, 'preflight', '3'],
                       cwd=WORK, capture_output=True, text=True, encoding='utf-8', errors='replace')
    return sum(1 for line in r.stdout.splitlines() if 'Building ' in line or 'needs to be rebuilt' in line and False)


def log(msg):
    with open(LANES / 'driver.log', 'a', encoding='utf-8') as f:
        f.write(time.strftime('%Y-%m-%d %H:%M:%S ') + msg + '\n')


def drive():
    running = {}   # job id -> (Popen, spec)
    last = 0.0
    log('driver start')
    # Restart recovery: a job left in running/ by a dead driver has no owner and no receipt.
    # Requeue it (lake makes a finished build a no-op), so its submitter still gets a receipt.
    for rf in RUN.glob('*.json'):
        try:
            spec = json.loads(rf.read_text(encoding='utf-8'))
        except Exception:
            continue
        rf.replace(Q / rf.name)
        log(f"recover {spec.get('target')} -> queue")
    while True:
        for jid, (proc, spec) in list(running.items()):
            if proc.poll() is not None:
                out = Path(spec['out']).read_text(encoding='utf-8', errors='replace')
                spec.update(rc=proc.returncode, ended=time.time(), output=out[-4000:])
                (DONE / f'{jid}.json').write_text(json.dumps(spec), encoding='utf-8')
                (RUN / f'{jid}.json').unlink(missing_ok=True)
                learn(spec['target'], out)
                log(f"done {spec['target']} rc={proc.returncode}")
                del running[jid]
        # Own-tree shedding (skill: kill only owned trees, by PID): if the host nears the floor,
        # stop the YOUNGEST owned job's whole tree and requeue it once, before the global
        # watchdog has to pick a victim it does not own.
        if running:
            phys0, commit0 = mem()
            if phys0 < FLOOR + 0.5 or commit0 < FLOOR + 0.5:
                jid, (proc, spec) = max(running.items(), key=lambda kv: kv[1][1]['started'])
                subprocess.run(['taskkill', '/T', '/F', '/PID', str(proc.pid)], capture_output=True)
                proc.wait()
                (RUN / f'{jid}.json').unlink(missing_ok=True)
                tries = int(spec.get('shed', 0)) + 1
                if tries <= 1:
                    (Q / f'{jid}.json').write_text(json.dumps({k: spec[k] for k in spec if k not in ('started', 'out')} | {'shed': tries}), encoding='utf-8')
                else:
                    spec.update(rc=99, ended=time.time(), output='lanes: shed twice for memory; held')
                    (DONE / f'{jid}.json').write_text(json.dumps(spec), encoding='utf-8')
                log(f"shed {spec['target']} phys={phys0:.1f} commit={commit0:.1f} tries={tries}")
                del running[jid]
                last = time.time() + 30
        def _mt(p):
            try: return p.stat().st_mtime
            except OSError: return float('inf')
        queued = sorted(Q.glob('*.json'), key=_mt)
        busy = {s['target'] for _, s in running.values()}
        pick = None
        if (queued and not (LANES / 'PAUSE').exists() and len(running) < MAXLANES
                and time.time() - last >= RAMP):
            phys, commit = mem()
            # manage-compute-campaigns envelope: free + own live workers - floor - margin must
            # cover the REMAINING forecast peaks of every running job plus the new one.
            use = tree_usage([proc.pid for proc, _ in running.values()])
            own_ws = sum(u[0] for u in use.values()); own_c = sum(u[1] for u in use.values())
            need_c = sum(est(s['target'])[0] for _, s in running.values())
            need_w = sum(est(s['target'])[1] for _, s in running.values())
            env_w = min(24.0, phys + own_ws - FLOOR - MARGIN)
            env_c = commit + own_c - FLOOR - MARGIN
            # Backfill: the first queued job (priority order) that fits starts, so light
            # modules run beside a heavy one instead of waiting behind it.
            for qf in queued[:200]:
                try:
                    s = json.loads(qf.read_text(encoding='utf-8'))
                except (json.JSONDecodeError, OSError):
                    continue   # being written by a submitter (28 Oct 11:51 crash), or just taken
                if s['target'] in busy:
                    continue
                ec, ew = est(s['target'])
                bb = float(s.get('budget', 3))
                if bb > 3:   # an explicit large budget (assembly roots) overrides a light class peak
                    ec, ew = max(ec, 1.75 * bb + 1.0), max(ew, bb)
                if need_w + ew <= env_w and need_c + ec <= env_c:
                    pick, spec = qf, s
                    break
                # Starvation guard (skill: reserve headroom for a ready large or critical job):
                # if this job has waited > STARVE seconds, nothing behind it may backfill.
                if time.time() - float(s.get('submitted', time.time())) > STARVE:
                    break
        if pick and not spec.get('cmd'):
            why = registry_refusal(spec['target'])
            if why:
                spec.update(rc=96, ended=time.time(), output='lanes: refused: ' + why)
                (DONE / f'{pick.stem}.json').write_text(json.dumps(spec), encoding='utf-8')
                pick.unlink(missing_ok=True)
                log(f"refuse-registry {spec['target']}")
                pick = None
        if pick and not spec.get('cmd'):
            # One lake build compiles every stale dependency in parallel (~1.5-2.5 GB each),
            # which is how a single root took ~15 GB of commit on 28 Oct 11:32. Refuse a build
            # whose stale frontier is more than the module itself, unless 'allow_frontier' is set.
            n = stale_count(spec['target'])
            if n > int(spec.get('allow_frontier', 1)):
                spec.update(rc=98, ended=time.time(), output=f'lanes: refused, stale frontier = {n} modules; build the leaves first (or submit with allow_frontier)')
                (DONE / f'{pick.stem}.json').write_text(json.dumps(spec), encoding='utf-8')
                pick.unlink(missing_ok=True)
                log(f"refuse {spec['target']} frontier={n}")
                pick = None
        if pick:
            b = float(spec.get('budget', 3))
            if True:
                jid = pick.stem
                pick.rename(RUN / pick.name)
                # Output goes to a file: a PIPE read only at exit deadlocks once the
                # child's output fills the pipe buffer (happened 28 Oct 09:16-09:40).
                spec['out'] = str(OUTD / f'{jid}.txt')
                fh = open(spec['out'], 'w', encoding='utf-8')
                argv = spec.get('cmd') or [str(PY), '-I', 'scripts/claude/run_guarded.py',
                                           spec['target'], 'build', str(int(b))]
                proc = subprocess.Popen(argv, cwd=spec.get('cwd', str(WORK)),
                                        stdout=fh, stderr=subprocess.STDOUT,
                                        env={**os.environ, 'LEAN_NUM_THREADS': THREADS})
                fh.close()
                spec['started'] = time.time()
                running[jid] = (proc, spec)
                last = time.time()
                log(f"start {spec['target']} est={ec:.1f}GB phys={phys:.1f} commit={commit:.1f} lanes={len(running)}")
        time.sleep(3)


def submit(target, budget=3, cmd=None):
    jid = f'{int(time.time()*1000)}-{uuid.uuid4().hex[:6]}'
    spec = {'target': target, 'budget': budget, 'submitted': time.time()}
    if cmd:   # arbitrary heavy job (lean --run generator, Python), admitted like a build
        spec.update(cmd=cmd, cwd=os.getcwd())
    tmp = Q / f'{jid}.tmp'
    tmp.write_text(json.dumps(spec), encoding='utf-8')
    tmp.replace(Q / f'{jid}.json')   # atomic: the driver never sees a half-written spec
    while not (DONE / f'{jid}.json').exists():
        time.sleep(5)
    r = json.loads((DONE / f'{jid}.json').read_text(encoding='utf-8'))
    print(r.get('output', ''))
    print(json.dumps({k: r.get(k) for k in ('target', 'rc', 'budget')}))
    sys.exit(r['rc'])


if __name__ == '__main__':
    if sys.argv[1] == 'drive':
        drive()
    elif sys.argv[1] == 'submit':
        submit(sys.argv[2], float(sys.argv[3]) if len(sys.argv) > 3 else 3)
    elif sys.argv[1] == 'run':
        # lanes.py run <label> <budgetGB> -- <command ...>
        i = sys.argv.index('--')
        submit('job.' + sys.argv[2], float(sys.argv[3]), cmd=sys.argv[i + 1:])
