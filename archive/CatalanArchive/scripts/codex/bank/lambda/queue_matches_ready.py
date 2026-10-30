"""Admit selected rational line-count assemblies after physical count parents and first qualification."""
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
from pathlib import Path
import json,subprocess,sys,time
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/lambda';D=R.parent/'tools/lanes/done'
def accepted():
 latest={}
 for p in D.glob('*.json'):
  try:r=json.loads(p.read_text(encoding='utf-8-sig'))
  except (OSError,ValueError):continue
  t=r.get('target','')
  if '.Lambda.' in t and (t not in latest or r.get('submitted',0)>latest[t].get('submitted',0)):latest[t]=r
 return {t for t,r in latest.items() if r.get('rc')==0}
def run(t):
 p=subprocess.run([sys.executable,'-I','-X','utf8','scripts/codex/bank/lambda/lane_client.py',t],cwd=R,capture_output=True,text=True,encoding='utf-8')
 (S/(t.replace('.','_')+'.client.txt')).write_text(p.stdout+'\n'+p.stderr,encoding='utf-8')
 print(t,'rc=',p.returncode,flush=True)
 return t,p.returncode
pending=set(json.loads((S/'matches-manifest.json').read_text(encoding='utf-8')))
results=[];active={};start=time.monotonic()
with ThreadPoolExecutor(max_workers=2) as pool:
 while pending or active:
  done=accepted();pending-=done
  ready=sorted(t for t in pending if 'CatalanCore.Uniform.Bank.Lambda.RankMatch.C1S00' in done and t.replace('.RankMatch.','.RankCount.') in done)
  while ready and len(active)<2:
   t=ready.pop(0);pending.remove(t);active[pool.submit(run,t)]=t
  if active:
   finished,_=wait(active,timeout=10,return_when=FIRST_COMPLETED)
   for f in finished:
    active.pop(f);t,rc=f.result();results.append({'target':t,'rc':rc})
    if rc:pending.clear()
  elif pending:time.sleep(10)
  if time.monotonic()-start>14400:
   print('Bounded four-hour supervisor limit; unlaunched',len(pending),flush=True);break
(S/'matches-continuation-results.json').write_text(json.dumps({'results':results,'unlaunched':sorted(pending)},indent=2),encoding='utf-8')
