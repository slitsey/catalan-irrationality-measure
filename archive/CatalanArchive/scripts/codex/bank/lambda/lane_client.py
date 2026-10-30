"""Mandatory preflight-first shared-lane client with dependency ordering and adoption."""
from pathlib import Path
from contextlib import contextmanager
import json,msvcrt,os,re,subprocess,sys,time
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/lambda';L=R.parent/'tools/lanes'
LOCKS=S/'preflight-locks';LOCKS.mkdir(exist_ok=True)
RETired={'SigmaQuarter','SigmaQuarterContour','QuarterContour','SigmaThirds','SigmaHybS'}
class BuildFailure(Exception):
 def __init__(self,target,rc):self.target=target;self.rc=rc;super().__init__(f'{target}: rc={rc}')
def build_budget(t):
 return 8 if t.startswith('CatalanCore.Uniform.Bank.Lambda.Cover.') and t.endswith(('.Check','.Decay')) else 2.5

def read_json(p):
 try:return json.loads(p.read_text(encoding='utf-8-sig'))
 except (OSError,ValueError):return None
def latest_receipt(t):
 rs=[r for p in (L/'done').glob('*.json') if (r:=read_json(p)) and r.get('target')==t]
 return max(rs,key=lambda r:r.get('submitted',0)) if rs else None
@contextmanager
def target_lock(t):
 p=LOCKS/(t+'.lock')
 with p.open('a+b') as f:
  if f.tell()==0:f.write(b'0');f.flush()
  while True:
   try:f.seek(0);msvcrt.locking(f.fileno(),msvcrt.LK_NBLCK,1);break
   except OSError:time.sleep(2)
  try:yield
  finally:f.seek(0);msvcrt.locking(f.fileno(),msvcrt.LK_UNLCK,1)
def pending_job(t):
 for d in ['running','queue']:
  for p in (L/d).glob('*.json'):
   r=read_json(p)
   if r and r.get('target')==t:return p.stem
 return None
def save_receipt(t,r):
 out=Path(r['out']) if r.get('out') else None
 body=out.read_text(encoding='utf-8',errors='replace') if out and out.exists() else r.get('output','')
 (S/(t.replace('.','_')+'.lane.txt')).write_text(body+'\n'+json.dumps({k:r.get(k) for k in ['target','rc','budget']})+'\n',encoding='utf-8')
def adopt(t,jid):
 print('Adopting existing shared-lane job',t,jid,flush=True)
 deadline=time.monotonic()+14400
 while time.monotonic()<deadline:
  r=read_json(L/'done'/(jid+'.json'))
  if r:
   save_receipt(t,r)
   if r.get('rc') not in (0,98):raise BuildFailure(t,r.get('rc',1))
   return r
  time.sleep(5)
 raise BuildFailure(t,75)
def preflight(t):
 p=subprocess.run([sys.executable,'-I','-X','utf8','scripts/claude/run_guarded.py',t,'preflight','3'],cwd=R,capture_output=True,text=True,encoding='utf-8',errors='replace')
 (S/(t.replace('.','_')+'.preflight.txt')).write_text(p.stdout+'\n'+p.stderr,encoding='utf-8')
 leaves=list(dict.fromkeys(re.findall(r'Building ([A-Za-z0-9_.]+)',p.stdout)))
 print('Preflight',t,'rc=',p.returncode,'stale=',leaves,flush=True)
 if p.returncode and not leaves:raise BuildFailure(t,p.returncode)
 return p,leaves
def build(t,stack=(),count=None):
 if t in stack:raise RuntimeError('cyclic preflight frontier: '+repr(stack+(t,)))
 if RETired.intersection(t.split('.')):raise RuntimeError('retired atomic dependency held: '+t)
 if count is None:count=[0]
 with target_lock(t):
  jid=pending_job(t)
  if jid:adopt(t,jid)
  for retry in range(15):
   pf,leaves=preflight(t)
   deps=[x for x in leaves if x!=t]
   if deps:
    for dep in deps:build(dep,stack+(t,),count)
    continue
   old=latest_receipt(t)
   if not leaves and pf.returncode==0 and old and old.get('rc')==0:
    save_receipt(t,old);return 0
   # Only the requested target may be stale at this submission boundary.
   if leaves and leaves!=[t]:raise RuntimeError('unresolved frontier '+repr(leaves))
   jid=pending_job(t)
   if jid:adopt(t,jid);continue
   count[0]+=1
   if count[0]>100:raise RuntimeError('bounded 100-submit dependency pass exhausted')
   p=subprocess.run([sys.executable,'-I','-X','utf8','scripts/claude/lanes.py','submit',t,str(build_budget(t))],cwd=R,capture_output=True,text=True,encoding='utf-8',errors='replace')
   (S/(t.replace('.','_')+'.lane.txt')).write_text(p.stdout+'\n'+p.stderr,encoding='utf-8')
   print('Submitted after preflight',t,'rc=',p.returncode,flush=True)
   if p.returncode==0:return 0
   if p.returncode!=98:raise BuildFailure(t,p.returncode)
  raise RuntimeError('bounded preflight retry pass exhausted: '+t)
if __name__=='__main__':
 try:
  for t in sys.argv[1:]:build(t if '.' in t else 'CatalanCore.Uniform.Bank.Lambda.'+t)
 except BuildFailure as e:
  print(str(e),flush=True);sys.exit(e.rc)
