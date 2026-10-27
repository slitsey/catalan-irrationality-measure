"""Required D58 provider import closure, serial inspected leaves; no broad Lake build."""
import sys,subprocess,re,json,time
from pathlib import Path
sys.stdout.reconfigure(encoding='utf8')
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea');W=ROOT/'work/catalan-uniform';E=ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank';R=W/'scripts/uniform-phase0/run_guarded.py'
start=time.monotonic();records=[];done=set();limit=1800
class Checkpoint(Exception):pass

def invoke(t,mode):
 p=subprocess.run([sys.executable,str(R),t,mode,'4'],capture_output=True,text=True,encoding='utf8',errors='replace');print(p.stdout,flush=True);return p

def ensure(t,depth=0):
 if t in done:return
 if time.monotonic()-start>limit:raise Checkpoint('30 minute checkpoint before next leaf')
 if depth>30:raise RuntimeError('Unexpected import recursion')
 if any(x in t for x in ('PilotPotential','PilotArithmetic','Atomic')):raise RuntimeError('Unexpected retired pilot import: '+t)
 for _ in range(120):
  p=invoke(t,'preflight')
  if p.returncode==0:done.add(t);return
  f=re.findall(r'Building ([\w.]+)',p.stdout)
  if p.returncode!=3 or not f:raise RuntimeError('Unexpected preflight: '+t)
  if f==[t]:
   if time.monotonic()-start>limit:raise Checkpoint('30 minute checkpoint before next leaf')
   p=invoke(t,'build');rec=dict(target=t,rc=p.returncode,elapsed_seconds=time.monotonic()-start);records.append(rec);save('running')
   if p.returncode:raise RuntimeError('Build failed: '+t)
   done.add(t);return
  print('FRONTIER',t,len(f),flush=True)
  for a in f:
   if a==t:raise RuntimeError('Mixed target/dependency frontier')
   ensure(a,depth+1)
 raise RuntimeError('Exceeded bounded recursive rounds')

def save(status,error=None):
 (E/'provider-builds.json').write_text(json.dumps(dict(status=status,error=error,seconds=time.monotonic()-start,builds=records,completed_targets=sorted(done)),indent=2)+'\n')
try:
 ensure('CatalanMeasure.GenD.Uniform.Bank.Providers532');save('complete');print('D58_PROVIDERS_ACCEPTED',flush=True)
except Exception as ex:
 save('checkpoint'if isinstance(ex,Checkpoint)else'failed',str(ex));raise
