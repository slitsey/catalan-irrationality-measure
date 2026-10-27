"""Serial critical-lane targeted builds. Every build is preceded by an inspected no-build frontier."""
import sys,subprocess,json,re,time
from pathlib import Path
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea');WORK=ROOT/'work/catalan-uniform';EVID=ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/decay'
sys.stdout.reconfigure(encoding='utf8')
RUNNER=WORK/'scripts/uniform-phase0/run_guarded.py'
labels=['EnergyArithmetic','EnergyHigh','BlockData','BlockStream','Chi3FinalData','Chi3FinalStream','ThirdsFinalData','ThirdsFinalStream','LambdaFinalData','LambdaFinalStream','FifthsFinalData','FifthsFinalStream']
if len(sys.argv)>1:labels=sys.argv[1:]
results=[]
for label in labels:
    target='CatalanCore.Uniform.Decay.Optimization.'+label
    pre=subprocess.run([sys.executable,str(RUNNER),target,'preflight'],capture_output=True,text=True,encoding='utf8',errors='replace')
    (EVID/(label+'-preflight-console.txt')).write_text(pre.stdout+pre.stderr,encoding='utf8')
    frontier=re.findall(r'Building ([\w.]+)',pre.stdout)
    if pre.returncode==0:
        results.append(dict(target=target,status='UP_TO_DATE'));continue
    if pre.returncode!=3 or frontier!=[target]:
        print(pre.stdout,flush=True);raise RuntimeError('Unexpected stale frontier: '+repr(frontier))
    build=subprocess.run([sys.executable,str(RUNNER),target,'build'],capture_output=True,text=True,encoding='utf8',errors='replace')
    (EVID/(label+'-build-console.txt')).write_text(build.stdout+build.stderr,encoding='utf8')
    accepted=build.returncode==0 and 'Build completed successfully' in build.stdout
    rec=dict(target=target,rc=build.returncode,accepted=accepted)
    results.append(rec);(EVID/('critical-build-queue-extra.json'if len(sys.argv)>1 else'critical-build-queue.json')).write_text(json.dumps(dict(results=results),indent=2)+'\n')
    print(json.dumps(rec),flush=True)
    print('\n'.join(line for line in build.stdout.splitlines()if 'Built 'in line or 'Build completed successfully'in line or line.startswith('error:')),flush=True)
    if not accepted:raise RuntimeError('Build failed; preserve evidence and repair before any next target')
print('DECAY_CRITICAL_QUEUE_COMPLETED',flush=True)

