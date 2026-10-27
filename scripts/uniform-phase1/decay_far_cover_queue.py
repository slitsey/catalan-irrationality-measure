"""Concurrent bounded compressed-cover and local cost-profile jobs."""
import os,sys,json,time,subprocess,concurrent.futures
from pathlib import Path
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea');WORK=ROOT/'work/catalan-uniform';EVID=ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/decay';GUARD=ROOT/'work/tools/guard-proof-safe.ps1'
jobs=[('chi3','baseline'),('thirds+','baseline'),('lambda+','baseline'),('q5-a1','baseline'),('chi3','12'),('thirds+','12'),('lambda+','22'),('q5-a1','22')]
def run(job):
    f,v=job;label=f'far-cover-{f}-{v}';start=time.time()
    cmd=['powershell.exe','-NoProfile','-ExecutionPolicy','Bypass','-File',str(GUARD),'-Kind','python','-Dir',str(WORK),'-BudgetGB','2','-Exe',sys.executable,'-ArgString',f'scripts/uniform-phase1/decay_far_cover.py {f} {v}']
    with(EVID/(label+'.log')).open('w',encoding='utf8')as log:
        p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW);rc=p.wait()
    path=EVID/'far-covers'/f'cover-{f}-{v}.json';rec=json.loads(path.read_text())if path.exists()else None
    receipt=dict(frame=f,variant=v,rc=rc,accepted=bool(rc==0 and rec and rec.get('status')=='COMPLETE_E_COVER'),wrapper_seconds=time.time()-start)
    (EVID/(label+'-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');print('FAR_COVER_JOB '+json.dumps(receipt),flush=True);return receipt
with concurrent.futures.ThreadPoolExecutor(max_workers=6)as pool:results=list(pool.map(run,jobs))
(EVID/'far-cover-campaign.json').write_text(json.dumps(dict(status='COMPLETE'if all(r['accepted']for r in results)else'INCOMPLETE',GiB_per_worker=2,max_workers=6,results=results),indent=2)+'\n')
if not all(r['accepted']for r in results):raise SystemExit(1)

