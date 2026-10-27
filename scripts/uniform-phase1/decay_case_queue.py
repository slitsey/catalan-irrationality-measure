"""Bounded per-family performance artifacts and cost profiles."""
import sys,subprocess,concurrent.futures,json,time
from pathlib import Path
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea');WORK=ROOT/'work/catalan-uniform';EVID=ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/decay'
JOBS=[f for f in('chi3','thirds+','lambda+','q5-a1')]+['profile '+f for f in('chi3','thirds+','lambda+','q5-a1')]
def run(args):
    label='case-'+args.replace(' ','-');start=time.time()
    cmd=['powershell.exe','-NoProfile','-ExecutionPolicy','Bypass','-File',str(ROOT/'work/tools/guard-proof-safe.ps1'),'-Kind','python','-Dir',str(WORK),'-BudgetGB','1','-Exe',sys.executable,'-ArgString','scripts/uniform-phase1/decay_cases.py '+args]
    with(EVID/(label+'.log')).open('w',encoding='utf8')as log:
        p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW);rc=p.wait()
    result=dict(job=args,rc=rc,seconds=time.time()-start);print('CASE_JOB '+json.dumps(result),flush=True);return result
with concurrent.futures.ThreadPoolExecutor(max_workers=6)as pool:results=list(pool.map(run,JOBS))
(EVID/'case-campaign.json').write_text(json.dumps(dict(results=results),indent=2)+'\n')
if any(r['rc']for r in results):raise SystemExit(1)
