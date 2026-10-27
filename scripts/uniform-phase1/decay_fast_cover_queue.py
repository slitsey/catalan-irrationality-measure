"""Refill fast cover jobs in two lanes while old controls drain, then at most six."""
import os,sys,time,json,subprocess,concurrent.futures
from pathlib import Path
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea');WORK=ROOT/'work/catalan-uniform';EVID=ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/decay';GUARD=ROOT/'work/tools/guard-proof-safe.ps1'
jobs=[('chi3','baseline'),('thirds+','baseline'),('lambda+','baseline'),('q5-a1','baseline'),('thirds+','12'),('lambda+','22'),('q5-a1','22')]
def run(job):
    f,v=job;label=f'fast-cover-{f}-{v}';start=time.time()
    cmd=['powershell.exe','-NoProfile','-ExecutionPolicy','Bypass','-File',str(GUARD),'-Kind','python','-Dir',str(WORK),'-BudgetGB','1','-Exe',sys.executable,'-ArgString',f'scripts/uniform-phase1/decay_fast_cover.py {f} {v}']
    with(EVID/(label+'.log')).open('w',encoding='utf8')as log:
        p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW);rc=p.wait()
    path=EVID/'fast-covers'/f'cover-{f}-{v}.json';r=json.loads(path.read_text())if path.exists()else None
    rec=dict(frame=f,variant=v,rc=rc,accepted=bool(rc==0 and r and r.get('status')=='COMPLETE_E_COVER'),wrapper_seconds=time.time()-start)
    (EVID/(label+'-receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print('FAST_JOB '+json.dumps(rec),flush=True);return rec
active={};results=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=6)as pool:
    while jobs or active:
        # Terminal receipts are written only after the old native guard handle exited.
        old_done=all((EVID/f'far-cover-{f}-baseline-receipt.json').exists()for f in('chi3','thirds+','lambda+','q5-a1'))
        cap=6 if old_done else 2
        while jobs and len(active)<cap:
            j=jobs.pop(0);active[pool.submit(run,j)]=j
        done,_=concurrent.futures.wait(active,timeout=2,return_when=concurrent.futures.FIRST_COMPLETED)
        for future in done:results.append(future.result());del active[future]
(EVID/'fast-cover-campaign.json').write_text(json.dumps(dict(status='COMPLETE'if all(r['accepted']for r in results)else'INCOMPLETE',future_max_workers=6,GiB_per_worker=1,results=results),indent=2)+'\n')
if not all(r['accepted']for r in results):raise SystemExit(1)
