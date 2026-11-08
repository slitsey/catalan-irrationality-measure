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
import ctypes as C, json, os, re, subprocess, sys, time, uuid
# Receipts carry Lean output (non-ASCII); a cp1252 console made `submit` crash while printing.
try:
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
except (AttributeError, ValueError):
    pass
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
WORK = ROOT / 'work/catalan-uniform'
PY = Path(r'C:\Users\seanl\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
LANES = ROOT / 'work/tools/lanes'
Q, RUN, DONE, OUTD = LANES / 'queue', LANES / 'running', LANES / 'done', LANES / 'out'
for d in (Q, RUN, DONE, OUTD):
    d.mkdir(parents=True, exist_ok=True)
MAXLANES, RAMP, STARVE = 6, 2, 300
MAXGEN = 4   # at most this many capped `run` jobs (generators, receipts, probes) at once


def capped_run(spec):
    """A `run` job (target `job.*`) counts against MAXGEN unless its label starts with one of the
    exempt prefixes in LANES/gen-exempt.txt (short checks, audits, research screens)."""
    t = spec.get('target', '')
    if not (spec.get('cmd') and t.startswith('job.')):
        return False
    try:
        exempt = [l.strip() for l in (LANES / 'gen-exempt.txt').read_text(encoding='utf-8').splitlines()
                  if l.strip() and not l.lstrip().startswith('#')]
    except OSError:
        exempt = []
    return not any(t.startswith('job.' + e) for e in exempt)
# RAMP was 10 s; with a 7 s synchronous preflight per start the driver could not exceed ~2 lanes of
# 23 s median jobs (28 Oct 19:30). Preflights now run in a background pool and are cached.
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
# 1 Nov: a class-wide max learned from a killed runaway (CurvInst, 16 GB) put the Assembly class
# above what an idle host can offer, and every Assembly module (CurvFast: 9 s) waited forever.
# Forecasts are now per module, learned from successful builds only (latest value, so a fixed
# module's forecast comes back down); an unmeasured module uses the MEDIAN of its class's
# successful modules. peaks.json keeps the old class maxima only as a last fallback.
TLEARN = LANES / 'tpeaks.json'
def tpeaks():
    try: return json.loads(TLEARN.read_text(encoding='utf-8'))
    except Exception: return {}
def est(t):
    tp = tpeaks()
    ws = tp.get(t)
    if ws is None:
        sib = sorted(v for k, v in tp.items() if cls(k) == cls(t))
        ws = sib[len(sib) // 2] if sib else peaks().get(cls(t))
    return (1.75 * ws + 1.0, ws) if ws else (7.0, 3.5)
def reserve(spec, used=(0.0, 0.0)):
    """(commit, working set) GB held for a job: the larger of forecast and declared budget; a job
    already above that is growing, so it holds 1.25 x what it uses now."""
    ec, ew = est(spec['target'])
    bb = float(spec.get('budget', 3))
    own = tpeaks().get(spec['target'])
    if spec['target'].startswith('job.'):
        # 7 Nov: run jobs never learn their own peak (learn() reads Lean peaks only), so the
        # class median of every past job (8-11.5 GB) was held for 1 GB Python jobs and stalled
        # the queue with 15 GB free. A run job holds its declared budget; growth past it is
        # still caught by the 1.25 x use rule below.
        ew = max(bb, 1.0); ec = 1.75 * ew + 1.0
    elif own is not None:
        # 7 Nov: a module with its own measured peak holds 1.25 x that, not a habitual 4 GB
        # budget (1.2 GB builds were reserving 4 GB and leaving the host idle).
        ew = max(1.25 * own, 1.0); ec = 1.75 * ew + 1.0
    elif bb > 3:
        ec, ew = max(ec, 1.75 * bb + 1.0), max(ew, bb)
    ws, cm = used
    if ws > ew: ew = 1.25 * ws
    if cm > ec: ec = 1.25 * cm
    return ec, ew
def learn(t, out, rc=0):
    m = re.search(r'"lean_process_peak_working_sets_bytes": \{([^}]*)\}', out)
    if not m or rc != 0: return
    vals = [int(v) for v in re.findall(r': (\d+)', m.group(1))]
    if not vals: return
    tp = tpeaks(); tp[t] = max(vals) / 2**30
    TLEARN.write_text(json.dumps(tp, indent=1), encoding='utf-8')
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


def hold_refusal(target):
    """Coordinator hold: `hold.txt` lines `<target prefix>  # reason`. A matching job (build or
    `run` job, whose target is `job.<label>`) is refused with rc 95 and the reason; nothing builds."""
    try:
        lines = (LANES / 'hold.txt').read_text(encoding='utf-8').splitlines()
    except OSError:
        return None
    for l in lines:
        pre, _, why = l.partition('#')
        pre = pre.strip()
        if pre and (target == pre or target.startswith(pre)):
            return why.strip() or pre
    return None


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


_COUNT = re.compile(r'(?<![\d/.])(?<!/ )\b(\d{3,7})\b(?!\s*/)(?![\d.])')


def kcost_refusal(target):
    """1 Nov (Sean: "this must not happen again"): RInst/CurvInst ran 20+ min on `decide +kernel`
    over 1000-term exact sums nobody had costed. A NEW or MODIFIED module (cell data excepted) whose
    `decide +kernel` declaration iterates a count >= 200 must say what that costs: a `kcost:` comment
    in the declaration (measured or estimated kernel seconds, e.g. `-- kcost: 12 s measured 1 Nov`)."""
    if '.Cells.' in target:
        return None
    rel = target.replace('.', '/') + '.lean'
    clean = subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', rel], cwd=WORK,
                           capture_output=True).returncode == 0
    tracked = subprocess.run(['git', 'ls-files', '--error-unmatch', rel], cwd=WORK,
                             capture_output=True).returncode == 0
    if tracked and clean:
        return None
    try:
        src = (WORK / rel).read_text(encoding='utf-8')
    except OSError:
        return None
    bad = []
    for decl in re.split(r'\n(?=(?:private |protected )?(?:theorem|lemma|def|example|instance)\b)', src):
        if 'decide +kernel' not in decl:
            continue
        if 'kcost:' in decl:
            # 7 Nov (C7): a kcost comment that describes the work but states no seconds passed this
            # gate and the module ran ~3 h. The comment must carry a number of seconds.
            if not re.search(r'kcost:[^\n]*?\d+(?:\.\d+)?\s*(?:s|sec|seconds|ks)\b', decl):
                bad.append((decl.split(None, 2)[1] if len(decl.split()) > 1 else '?') + ' (kcost without seconds)')
            continue
        counts = [int(m.group(1)) for m in _COUNT.finditer(decl) if 200 <= int(m.group(1)) <= 10 ** 7]
        if counts:
            bad.append(decl.split(None, 2)[1] if len(decl.split()) > 1 else '?')
    if bad:
        return (f'kernel cost not stated: {", ".join(bad[:5])} run `decide +kernel` over a count >= 200; '
                'count the operations, measure one declaration, and add a `-- kcost: <s> s` comment (or redesign)')
    return None


def bigdata_refusal(spec):
    """7 Nov (C7, Sean: "how will you ensure this does not happen again"): a 15 GB single data module
    ran ~3 h. A build with budget > 8 GB is refused unless its target is listed in
    work/tools/lanes/bigok.txt (one module per line, added by the coordinator after a priced design)."""
    if spec.get('shed'):
        return None  # a shed job requeues at 1.5x its budget; that is the driver's own choice
    try:
        if float(spec.get('budget') or 0) <= 8.0:
            return None
    except (TypeError, ValueError):
        return None
    ok = LANES / 'bigok.txt'
    names = set(ok.read_text(encoding='utf-8').split()) if ok.exists() else set()
    if spec['target'] in names:
        return None
    return (f"budget {spec.get('budget')} GB > 8 GB for {spec['target']}: split the module or get the "
            'coordinator to add it to work/tools/lanes/bigok.txt after a measured price')


def stale_count(target):
    r = subprocess.run([str(PY), '-I', 'scripts/claude/run_guarded.py', target, 'preflight', '3'],
                       cwd=WORK, capture_output=True, text=True, encoding='utf-8', errors='replace')
    return sum(1 for line in r.stdout.splitlines() if 'Building ' in line or 'needs to be rebuilt' in line and False)


_IMPS = {}


def imports_of(target):
    """Direct imports of a module target (cached by source mtime); empty for `run` jobs and unknown files."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from closure_check import path_of, IMPORT
    f = path_of(target) if not target.startswith('job.') else None
    if not f:
        return set()
    mt = os.path.getmtime(f)
    if target not in _IMPS or _IMPS[target][0] != mt:
        with open(f, encoding='utf-8') as fh:
            _IMPS[target] = (mt, set(IMPORT.findall(fh.read(20000).split('\nnamespace', 1)[0])))
    return _IMPS[target][1]


def maxlanes():
    """Lane cap, read live from LANES/maxlanes.txt (default MAXLANES); memory admission still applies.
    31 Oct: a fixed 6 left 16 of 22 cores idle while hybrid modules queued (Sean: minimise wall clock)."""
    try:
        return max(1, int((LANES / 'maxlanes.txt').read_text(encoding='utf-8').split()[0]))
    except (OSError, ValueError, IndexError):
        return MAXLANES


def log(msg):
    with open(LANES / 'driver.log', 'a', encoding='utf-8') as f:
        f.write(time.strftime('%Y-%m-%d %H:%M:%S ') + msg + '\n')


def drive():
    running = {}   # job id -> (Popen, spec)
    last = 0.0
    pool = ThreadPoolExecutor(max_workers=4)
    pre = {}   # target -> (future, submitted_at)
    stall_since, stall_logged = None, 0.0
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
                learn(spec['target'], out, proc.returncode)
                log(f"done {spec['target']} rc={proc.returncode}")
                del running[jid]
        # Own-tree shedding (skill: kill only owned trees, by PID): if the host nears the floor,
        # stop the YOUNGEST owned job's whole tree and requeue it once, before the global
        # watchdog has to pick a victim it does not own.
        if running:
            phys0, commit0 = mem()
            # 1 Nov (Sean): kill only on a real shortage. The guard handles RAM first (over-budget
            # tree below 3 GB free, any tree below 2 GB); shedding is the next step, at 1.5 GB.
            if phys0 < FLOOR - 1.5 or commit0 < FLOOR + 0.5:
                jid, (proc, spec) = max(running.items(), key=lambda kv: kv[1][1]['started'])
                subprocess.run(['taskkill', '/T', '/F', '/PID', str(proc.pid)], capture_output=True)
                proc.wait()
                (RUN / f'{jid}.json').unlink(missing_ok=True)
                tries = int(spec.get('shed', 0)) + 1
                # 7 Nov: a shed is the driver's choice, not the job's failure. rc 99 after two sheds
                # left agents' output waiters hung for hours (ln-c3s, p2s-pot, p2s-lg0). Always
                # requeue, with 1.5 x the budget so reserve() holds enough on the next admission.
                nb = min(24.0, 1.5 * float(spec.get('budget', 3)))
                (Q / f'{jid}.json').write_text(json.dumps({k: spec[k] for k in spec if k not in ('started', 'out')} | {'shed': tries, 'budget': nb}), encoding='utf-8')
                log(f"shed {spec['target']} phys={phys0:.1f} commit={commit0:.1f} tries={tries}")
                del running[jid]
                last = time.time() + 30
        # Priority (Sean, 31 Oct: "410 jobs get priority"): `priority.txt` lists target prefixes,
        # highest first; then other builds; then `run` jobs (job.*). Within a rank, oldest first.
        try:
            prio = [l.split('#')[0].strip() for l in (LANES / 'priority.txt').read_text(encoding='utf-8').splitlines()]
            prio = [p for p in prio if p]
        except OSError:
            prio = []
        def _key(p):
            try:
                mt = p.stat().st_mtime
                t = json.loads(p.read_text(encoding='utf-8')).get('target', '')
            except (OSError, ValueError):
                return (len(prio) + 2, float('inf'))
            for i, pre_ in enumerate(prio):
                if t == pre_ or t.startswith(pre_ + '.') or t.startswith(pre_):
                    return (i, mt)
            return (len(prio) + (1 if t.startswith('job.') else 0), mt)
        queued = sorted(Q.glob('*.json'), key=_key)
        # A queue is a queue (Sean, 31 Oct): submit everything at once.  A build whose direct import is
        # still queued or running waits in the queue (no waves, no refusal); it is neither preflighted
        # nor admitted until that import's job has finished.
        specs = {}
        for qf in queued:
            try:
                specs[qf] = json.loads(qf.read_text(encoding='utf-8'))
            except (json.JSONDecodeError, OSError):
                pass
        pend = {t['target'] for t in specs.values()} | {s['target'] for _, s in running.values()}
        def blocked(t):
            return not t.get('cmd') and bool(imports_of(t['target']) & pend)
        npre = 0
        for qf in queued:
            t = specs.get(qf)
            if t is None or blocked(t) or t.get('cmd'):
                continue   # `run` jobs need no preflight and must not use up the preflight slots
            npre += 1
            if npre > 12:
                break
            if not t.get('cmd') and (t['target'] not in pre or time.time() - pre[t['target']][1] > 600):
                pre[t['target']] = (pool.submit(stale_count, t['target']), time.time())
        busy = {s['target'] for _, s in running.values()}
        pick = None
        first_ready = None
        if (queued and not (LANES / 'PAUSE').exists() and len(running) < maxlanes()
                and time.time() - last >= RAMP):
            phys, commit = mem()
            # manage-compute-campaigns envelope: free + own live workers - floor - margin must
            # cover the REMAINING forecast peaks of every running job plus the new one.
            use = tree_usage([proc.pid for proc, _ in running.values()])
            own_ws = sum(u[0] for u in use.values()); own_c = sum(u[1] for u in use.values())
            # 7 Nov (Sean: control reserved memory): each running job holds its declared budget
            # for life. Before, running jobs were charged only the class forecast (3.5 GB default
            # for `run` jobs, whatever budget they declared), while their actual use was added to
            # the envelope, so a job over its forecast made the host look emptier.
            res = [reserve(s, use.get(proc.pid, (0.0, 0.0))) for proc, s in running.values()]
            need_c = sum(r[0] for r in res)
            need_w = sum(r[1] for r in res)
            env_w = min(24.0, phys + own_ws - FLOOR - MARGIN)
            env_c = commit + own_c - FLOOR - MARGIN
            # Backfill: the first queued job (priority order) that fits starts, so light
            # modules run beside a heavy one instead of waiting behind it.
            pending_rank = None   # rank of a higher-priority build still in preflight
            for qf in queued[:200]:
                try:
                    s = json.loads(qf.read_text(encoding='utf-8'))
                except (json.JSONDecodeError, OSError):
                    continue   # being written by a submitter (28 Oct 11:51 crash), or just taken
                if s['target'] in busy or blocked(s):
                    continue
                # A lower-priority job may jump a higher one only if that one does not fit; a
                # build still in preflight might fit, so lower ranks wait for it (31 Oct: `run`
                # jobs otherwise took every lane right after a driver restart).
                if pending_rank is not None and _key(qf)[0] > pending_rank:
                    continue
                # Generator cap (replaces defer-generators.sh): while MAXGEN capped `run` jobs are
                # running, a queued capped `run` job waits so a freed lane goes to a module build.
                if capped_run(s) and sum(capped_run(r) for _, r in running.values()) >= MAXGEN:
                    continue
                if not s.get('cmd'):
                    f = pre.get(s['target'])
                    if f is None or not f[0].done():
                        if pending_rank is None:
                            pending_rank = _key(qf)[0]
                        continue   # preflight still running in the background
                ec, ew = reserve(s)
                if need_w + ew <= env_w and need_c + ec <= env_c:
                    pick, spec = qf, s
                    break
                if first_ready is None:
                    first_ready = (qf, s, ew)
                # No starvation hold (Sean, 31 Oct): "We must always be using all available space
                # that is safe. Small jobs can jump the queue if they fit now." Priority order
                # (priority.txt) gives critical jobs the first fit; anything else that fits runs.
            # 1 Nov: never deadlock. A forecast can exceed what an idle host offers (E2 09:54,
            # Assembly 11:13); with nothing of ours running, the first ready job starts alone and
            # the guard enforces the real limit.
            if pick is None and not running and first_ready is not None:
                pick, spec = first_ready[0], first_ready[1]
                log(f"admit-alone {spec['target']} forecast={first_ready[2]:.1f}GB env={env_w:.1f}GB")
        # 1 Nov: a queue that admits nothing for 5 min with nothing running is a stall; log it.
        if queued and not running and not pick and not (LANES / 'PAUSE').exists():
            if stall_since is None:
                stall_since = time.time()
            elif time.time() - stall_since > 300 and time.time() - stall_logged > 300:
                log(f"STALL queue={len(queued)} running=0 for {int(time.time() - stall_since)} s")
                stall_logged = time.time()
        else:
            stall_since = None
        if pick:
            why = hold_refusal(spec['target'])
            if why:
                spec.update(rc=95, ended=time.time(), output='lanes: held by coordinator: ' + why)
                (DONE / f'{pick.stem}.json').write_text(json.dumps(spec), encoding='utf-8')
                pick.unlink(missing_ok=True)
                log(f"refuse-hold {spec['target']}")
                pick = None
        if pick and spec.get('cmd') and os.path.basename(str(spec['cmd'][0])).lower() in ('lake', 'lake.exe'):
            # 31 Oct: a `run` job with a bare `lake.exe` killed the driver (not on PATH); direct lake
            # builds bypass the guard anyway. Builds go through `submit`.
            spec.update(rc=94, ended=time.time(), output='lanes: refused: direct lake command; use `submit <Module> <GB>`')
            (DONE / f'{pick.stem}.json').write_text(json.dumps(spec), encoding='utf-8')
            pick.unlink(missing_ok=True)
            log(f"refuse-lake {spec['target']}")
            pick = None
        if pick and not spec.get('cmd'):
            why = registry_refusal(spec['target']) or kcost_refusal(spec['target']) or bigdata_refusal(spec)
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
            n = pre.pop(spec['target'])[0].result()
            if n > int(spec.get('allow_frontier', 1)):
                n = stale_count(spec['target'])   # recheck fresh: a dependency may have just finished
            if n > int(spec.get('allow_frontier', 1)):
                spec.update(rc=98, ended=time.time(), output=f'lanes: refused, stale frontier = {n} modules; build the leaves first (or submit with allow_frontier)')
                (DONE / f'{pick.stem}.json').write_text(json.dumps(spec), encoding='utf-8')
                pick.unlink(missing_ok=True)
                log(f"refuse {spec['target']} frontier={n}")
                pick = None
        if pick:
            b = float(spec.get('budget', 3))
            # 28 Oct 20:45: roots submitted with budget 3 were guard-killed (cap 1.5x budget) although
            # their class peak was known. Give the guard at least the forecast working set x 1.2.
            gb = max(b, -(-1.2 * est(spec['target'])[1] // 1))
            # 1 Nov: the guard waits for free RAM >= budget + floor, so a raise above the free RAM
            # deadlocked EvalRefE2 (17 GB raise, 17.5 GB free, 25 min idle). Admission has already
            # checked the forecast peak fits; cap the raise at free - floor (still >= forecast +
            # margin, inside the guard's 1.5x kill cap).
            gb = max(b, min(gb, (phys - FLOOR) // 1))
            if gb > b:
                log(f"raise-budget {spec['target']} {b:.0f}->{gb:.0f}")
                b = gb
            if True:
                jid = pick.stem
                pick.rename(RUN / pick.name)
                # Output goes to a file: a PIPE read only at exit deadlocks once the
                # child's output fills the pipe buffer (happened 28 Oct 09:16-09:40).
                spec['out'] = str(OUTD / f'{jid}.txt')
                fh = open(spec['out'], 'w', encoding='utf-8')
                argv = spec.get('cmd') or [str(PY), '-I', 'scripts/claude/run_guarded.py',
                                           spec['target'], 'build', str(int(b))]
                try:
                    proc = subprocess.Popen(argv, cwd=spec.get('cwd', str(WORK)),
                                            stdout=fh, stderr=subprocess.STDOUT,
                                            env={**os.environ, 'LEAN_NUM_THREADS': THREADS})
                except OSError as e:
                    # A bad command must fail its own job, never the driver.
                    fh.close()
                    spec.update(rc=127, ended=time.time(), output=f'lanes: could not start: {e}')
                    (DONE / f'{jid}.json').write_text(json.dumps(spec), encoding='utf-8')
                    (RUN / pick.name).unlink(missing_ok=True)
                    log(f"fail-start {spec['target']} {e}")
                    continue
                fh.close()
                spec['started'] = time.time()
                running[jid] = (proc, spec)
                last = time.time()
                log(f"start {spec['target']} est={ec:.1f}GB phys={phys:.1f} commit={commit:.1f} lanes={len(running)}")
        time.sleep(3)


def manifest_gate(target):
    """6 Nov (Sean: nothing built twice): route-I build manifest, checked in the submitter so it
    applies without restarting the driver. Returns an exit code to stop with, or None to queue."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import manifest
    owner = os.environ.get('LANES_OWNER', '')
    r = manifest.refusal(target, owner)
    if r is None:
        return None
    rc, msg = r
    if rc == 'check-stale':
        n = stale_count(target)
        if n == 0:
            print(f'lanes: {msg}; up to date, nothing built')
            print(json.dumps({'target': target, 'rc': 0, 'budget': None}))
            return 0
        rc, msg = 93, (f'{msg}, but an import changed after it was built (stale frontier {n}); '
                       'a rebuild needs coordinator rebuild-ok (build-once rule)')
    print(f'lanes: refused by manifest: {msg}')
    print(json.dumps({'target': target, 'rc': rc, 'budget': None}))
    return rc


def submit(target, budget=3, cmd=None):
    if not cmd:
        g = manifest_gate(target)
        if g is not None:
            sys.exit(g)
    jid = f'{int(time.time()*1000)}-{uuid.uuid4().hex[:6]}'
    spec = {'target': target, 'budget': budget, 'submitted': time.time(),
            'owner': os.environ.get('LANES_OWNER', '')}
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
    if not cmd and r['rc'] == 0:
        import manifest
        manifest.mark_built(target, 0)
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
