"""Final robust lambda24 qualification; preserve all prior controls."""
import sys,subprocess,time
from pathlib import Path
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea');WORK=ROOT/'work/catalan-uniform';EVID=ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/decay';GUARD=ROOT/'work/tools/guard-proof-safe.ps1'
for label,args in [('lambda24-cover','decay_fast_cover.py lambda+ 23'),('lambda24-moments','decay_moment_kernel.py lambda+ 23 Lambda24Moments'),('lambda24-case','decay_cases.py lambda+')]:
    cmd=['powershell.exe','-NoProfile','-ExecutionPolicy','Bypass','-File',str(GUARD),'-Kind','python','-Dir',str(WORK),'-BudgetGB','1','-Exe',sys.executable,'-ArgString','scripts/uniform-phase1/'+args]
    with(EVID/(label+'.log')).open('w',encoding='utf8')as log:result=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW)
    print(label,'rc',result.returncode,flush=True)
    if result.returncode:raise SystemExit(result.returncode)
result=subprocess.run([sys.executable,str(WORK/'scripts/uniform-phase1/decay_build_queue.py'),'Lambda24FinalData','Lambda24FinalStream','Lambda24Moments','FinalAudit'])
raise SystemExit(result.returncode)
