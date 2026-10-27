"""Bounded serialized leaf builds for inspected scalar D58 qualification closure."""
import sys,subprocess,re,json
from pathlib import Path
sys.stdout.reconfigure(encoding='utf8')
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea');W=ROOT/'work/catalan-uniform';E=ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank';R=W/'scripts/uniform-phase0/run_guarded.py'
allowed={'CatalanMeasure.GenD.PayW','CatalanMeasure.GenD.Budget','CatalanMeasure.GenD.D58.Budget','CatalanMeasure.GenD.D58.Budget590','CatalanMeasure.GenD.Uniform.Bank.Budget532'}
records=[]
def invoke(t,mode):
 p=subprocess.run([sys.executable,str(R),t,mode,'3'],capture_output=True,text=True,encoding='utf8',errors='replace');print(p.stdout,flush=True);return p

def ensure(t):
 assert t in allowed
 for _ in range(10):
  p=invoke(t,'preflight')
  if p.returncode==0:return
  f=re.findall(r'Building ([\w.]+)',p.stdout)
  if p.returncode!=3 or not f:raise RuntimeError('Unexpected frontier')
  if f==[t]:
   p=invoke(t,'build');records.append(dict(target=t,rc=p.returncode));(E/'scalar-builds.json').write_text(json.dumps(records,indent=2)+'\n')
   if p.returncode:raise RuntimeError('Build failed')
   return
  for a in f:
   if a not in allowed:raise RuntimeError('Non-scalar frontier: '+a)
   ensure(a)
 raise RuntimeError('Exceeded recursive bound')
ensure('CatalanMeasure.GenD.Uniform.Bank.Budget532')
