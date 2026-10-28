"""Shared memory-aware build lanes (Claude, 28 Oct 2026).

One driver admits guarded builds from every agent, so the host stays full but never
runs out of physical memory or commit charge.

    driver:  <python> -I scripts/claude/lanes.py drive
    agent:   <python> -I scripts/claude/lanes.py submit <Module.Name> [budgetGB]
             (blocks until the build ends; prints the receipt JSON; exit code = rc)

Admission rule: start the next queued job (FIFO) when
  running < MAXLANES,
  free physical - budget >= PHYS_RESERVE,
  free commit   - budget >= COMMIT_RESERVE,
and at least RAMP seconds have passed since the last start, so the previous job
can reach its peak before the next one is admitted. Jobs are run through
run_guarded.py (budget enforced by the guard). The driver never kills a job.
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
MAXLANES, PHYS_RESERVE, COMMIT_RESERVE, RAMP, YOUNG = 6, 3.5, 5.0, 10, 150
THREADS = '4'   # lanes run in parallel, so each lean needs few worker threads (default = 22 cores)
PHYS_PER_GB, COMMIT_PER_GB = 0.7, 1.2   # measured: 3 GB budget -> ~2 GB working set, ~3.6 GB commit
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


def log(msg):
    with open(LANES / 'driver.log', 'a', encoding='utf-8') as f:
        f.write(time.strftime('%Y-%m-%d %H:%M:%S ') + msg + '\n')


def drive():
    running = {}   # job id -> (Popen, spec)
    last = 0.0
    log('driver start')
    while True:
        for jid, (proc, spec) in list(running.items()):
            if proc.poll() is not None:
                out = Path(spec['out']).read_text(encoding='utf-8', errors='replace')
                spec.update(rc=proc.returncode, ended=time.time(), output=out[-4000:])
                (DONE / f'{jid}.json').write_text(json.dumps(spec), encoding='utf-8')
                (RUN / f'{jid}.json').unlink(missing_ok=True)
                log(f"done {spec['target']} rc={proc.returncode}")
                del running[jid]
        queued = sorted(Q.glob('*.json'), key=lambda p: p.stat().st_mtime)
        busy = {s['target'] for _, s in running.values()}
        pick = None
        for qf in queued:
            s = json.loads(qf.read_text(encoding='utf-8'))
            if s['target'] not in busy:
                pick, spec = qf, s
                break
        if (pick and not (LANES / 'PAUSE').exists() and len(running) < MAXLANES
                and time.time() - last >= RAMP):
            phys, commit = mem()
            b = float(spec.get('budget', 3))
            young = sum(float(s.get('budget', 3)) for _, s in running.values()
                        if time.time() - s['started'] < YOUNG)
            if (phys - PHYS_PER_GB * (b + young) >= PHYS_RESERVE
                    and commit - COMMIT_PER_GB * (b + young) >= COMMIT_RESERVE):
                jid = pick.stem
                pick.rename(RUN / pick.name)
                # Output goes to a file: a PIPE read only at exit deadlocks once the
                # child's output fills the pipe buffer (happened 28 Oct 09:16-09:40).
                spec['out'] = str(OUTD / f'{jid}.txt')
                fh = open(spec['out'], 'w', encoding='utf-8')
                proc = subprocess.Popen([str(PY), '-I', 'scripts/claude/run_guarded.py',
                                         spec['target'], 'build', str(int(b))], cwd=WORK,
                                        stdout=fh, stderr=subprocess.STDOUT,
                                        env={**os.environ, 'LEAN_NUM_THREADS': THREADS})
                fh.close()
                spec['started'] = time.time()
                running[jid] = (proc, spec)
                last = time.time()
                log(f"start {spec['target']} budget={b} phys={phys:.1f} commit={commit:.1f} lanes={len(running)}")
        time.sleep(3)


def submit(target, budget=3):
    jid = f'{int(time.time()*1000)}-{uuid.uuid4().hex[:6]}'
    (Q / f'{jid}.json').write_text(json.dumps({'target': target, 'budget': budget,
                                               'submitted': time.time()}), encoding='utf-8')
    while not (DONE / f'{jid}.json').exists():
        time.sleep(5)
    r = json.loads((DONE / f'{jid}.json').read_text(encoding='utf-8'))
    print(r.get('output', ''))
    print(json.dumps({k: r[k] for k in ('target', 'rc', 'budget')}))
    sys.exit(r['rc'])


if __name__ == '__main__':
    if sys.argv[1] == 'drive':
        drive()
    elif sys.argv[1] == 'submit':
        submit(sys.argv[2], float(sys.argv[3]) if len(sys.argv) > 3 else 3)
