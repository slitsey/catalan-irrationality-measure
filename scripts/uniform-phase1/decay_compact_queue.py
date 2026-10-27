"""Native bounded numerical dispatcher; all solver children use the shared guard."""
import subprocess,sys,json,concurrent.futures,time,os
from pathlib import Path
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
WORK=ROOT/'work/catalan-uniform'
EVID=ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/decay'
GUARD=ROOT/'work/tools/guard-proof-safe.ps1'
jobs=[('thirds+',12),('lambda+',12),('q5-a1',12),('chi3',20),('thirds+',20),('lambda+',20),('q5-a1',20)]
def run(job):
    frame,budget=job;label=f'compact-{frame}-{budget}'
    env=os.environ.copy();env['SCOPE_THREADS']='1';env['PYTHONDONTWRITEBYTECODE']='1'
    cmd=['powershell.exe','-NoProfile','-ExecutionPolicy','Bypass','-File',str(GUARD),'-Kind','python','-Dir',str(WORK),'-BudgetGB','3','-Exe',sys.executable,'-ArgString',f'scripts/uniform-phase1/decay_compact.py {frame} {budget}']
    started=time.time()
    with (EVID/(label+'.log')).open('w',encoding='utf8') as out:
        p=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,env=env,creationflags=subprocess.CREATE_NO_WINDOW)
        rc=p.wait()
    path=EVID/(label+'.json');record=json.loads(path.read_text()) if path.exists() else None
    receipt=dict(job=list(job),rc=rc,seconds=time.time()-started,accepted=bool(rc==0 and record and record.get('status')=='ACCEPTED_F'),worker_peak_working_set_bytes=record.get('worker_peak_working_set_bytes') if record else None,record=str(path))
    (EVID/(label+'-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print('JOB '+json.dumps(receipt),flush=True)
    return receipt
# Stage 2 qualifies two contemporaneous workers before any wider admission.
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    first=list(pool.map(run,jobs[:2]))
assert all(r['accepted'] for r in first)
assert all(r['worker_peak_working_set_bytes']<1500*1024**2 for r in first)
# These first jobs establish real memory below the conservative 3GiB reservation.
# Five 3GiB workers + parent's 4GiB build remain below shared26GiB pool;
# the guard still enforces physical-free admission and3GiB floor.
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
    rest=list(pool.map(run,jobs[2:]))
allrows=first+rest
(EVID/'compact-campaign.json').write_text(json.dumps(dict(status='COMPLETE' if all(r['accepted'] for r in allrows) else 'FAILED',max_workers=5,threads_per_worker=1,reservation_GiB_per_worker=3,jobs=allrows),indent=2)+'\n')
if not all(r['accepted'] for r in allrows):raise SystemExit(1)
print('COMPACT_CAMPAIGN_COMPLETE',flush=True)
