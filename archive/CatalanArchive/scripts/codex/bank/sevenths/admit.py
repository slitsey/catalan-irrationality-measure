"""Required explicit preflight and dependency-first admission, shared by sevenths submitters."""
from pathlib import Path
import json, re, subprocess, sys, threading, time
ROOT=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform')
LANES=ROOT.parent/'tools/lanes'
HERE=Path(__file__).parent
OUT=HERE/'admission-receipts'
OUT.mkdir(exist_ok=True)
guard=threading.Lock()
locks={}
def target_lock(target):
    with guard:
        return locks.setdefault(target, threading.RLock())
def queued(target):
    for folder in ('running','queue'):
        for path in (LANES/folder).glob('*.json'):
            try:
                if json.loads(path.read_text(encoding='utf-8-sig')).get('target')==target:
                    return path.stem
            except (OSError,ValueError):
                pass
    return None
def ensure(target, trail=(), budget=2.5):
    if target in trail:
        raise RuntimeError('cyclic stale dependency: '+repr(trail+(target,)))
    with target_lock(target):
        for attempt in range(4):
            job=queued(target)
            if job:
                path=LANES/'done'/(job+'.json')
                while not path.exists():
                    time.sleep(3)
                r=json.loads(path.read_text(encoding='utf-8-sig'))
                return int(r['rc'])
            start=time.time()
            p=subprocess.run([sys.executable,'-I','-X','utf8','scripts/claude/run_guarded.py',
                              target,'preflight','3'],cwd=ROOT,capture_output=True,text=True,
                             encoding='utf-8',errors='replace')
            log=None
            for line in p.stdout.splitlines():
                try:
                    meta=json.loads(line)
                    if meta.get('target')==target and meta.get('mode')=='preflight':
                        log=Path(meta['log'])
                except (ValueError,TypeError,AttributeError):
                    pass
            if log is None:
                raise RuntimeError('preflight did not return its own log: '+target+' '+p.stdout+p.stderr)
            text=log.read_text(encoding='utf-8')
            stale=list(dict.fromkeys(re.findall(r'Building ([A-Za-z0-9_.]+)',text)))
            receipt=dict(target=target,started=start,ended=time.time(),rc=p.returncode,
                         log=str(log),stale=stale)
            (OUT/(target.replace('.','_')+'-'+str(time.time_ns())+'.json')).write_text(
                json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
            if p.returncode==0:
                return 0
            if p.returncode!=3 or not stale:
                print(p.stdout+p.stderr,flush=True)
                return p.returncode or 1
            deps=[d for d in stale if d!=target]
            if deps:
                for dep in deps:
                    rc=ensure(dep,trail+(target,))
                    if rc:
                        return rc
                continue
            # This exact preflight has proved that no stale dependency remains.
            p=subprocess.run([sys.executable,'-I','-X','utf8','scripts/claude/lanes.py',
                              'submit',target,str(budget)],cwd=ROOT,capture_output=True,text=True,
                             encoding='utf-8',errors='replace')
            (OUT/(target.replace('.','_')+'-'+str(time.time_ns())+'.lane.txt')).write_text(
                p.stdout+p.stderr,encoding='utf-8')
            print(target,'shared-driver rc=',p.returncode,flush=True)
            return p.returncode
        raise RuntimeError('stale frontier changed four times: '+target)
