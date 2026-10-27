"""Bounded source-bound cover dispatcher; all jobs admitted by the shared memory guard."""
import os,sys,json,time,subprocess,concurrent.futures
from pathlib import Path
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea');WORK=ROOT/'work/catalan-uniform'
EVID=ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/decay'
GUARD=ROOT/'work/tools/guard-proof-safe.ps1'
jobs=[(f,v) for v in ('baseline','12','20') for f in ('chi3','thirds+','lambda+','q5-a1') if not(EVID/f'cover-{f}-{v}.json').exists()]
def job(j):
    f,v=j;label=f'cover-{f}-{v}';started=time.time();env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    cmd=['powershell.exe','-NoProfile','-ExecutionPolicy','Bypass','-File',str(GUARD),'-Kind','python','-Dir',str(WORK),'-BudgetGB','2','-Exe',sys.executable,'-ArgString',f'scripts/uniform-phase1/decay_cover.py {f} {v}']
    with(EVID/(label+'.log')).open('w',encoding='utf8')as log:
        p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,env=env,creationflags=subprocess.CREATE_NO_WINDOW);rc=p.wait()
    path=EVID/(label+'.json');rec=json.loads(path.read_text())if path.exists()else None
    receipt=dict(frame=f,variant=v,rc=rc,accepted=bool(rc==0 and rec and rec.get('status')=='COMPLETE_E_COVER'),wrapper_seconds=time.time()-started)
    (EVID/(label+'-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');print('COVER_JOB '+json.dumps(receipt),flush=True);return receipt
# Prior compact chi3 worker completed a full cover in60s; memory is small.
# Eight2GiB reservations + parent's4GiB Lean job leave6GiB of26GiB pool
# for closure and other authorized lanes; guard still gates physical free RAM.
with concurrent.futures.ThreadPoolExecutor(max_workers=8)as pool:results=list(pool.map(job,jobs))
(EVID/'cover-campaign.json').write_text(json.dumps(dict(status='COMPLETE'if all(r['accepted']for r in results)else'INCOMPLETE',max_workers=8,GiB_per_worker=2,results=results),indent=2)+'\n')
print('COVER_CAMPAIGN_FINISHED',flush=True)
if not all(r['accepted']for r in results):raise SystemExit(1)
