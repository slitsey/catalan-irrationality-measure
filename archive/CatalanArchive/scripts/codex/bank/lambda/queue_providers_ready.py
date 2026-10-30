"""Qualify and queue physical load facts and member prices without occupying shared lanes."""
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
from pathlib import Path
import json,re,subprocess,sys,time
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/lambda';D=R.parent/'tools/lanes/done'
def accepted():
 latest={}
 for p in D.glob('*.json'):
  try:r=json.loads(p.read_text(encoding='utf-8-sig'))
  except (OSError,ValueError):continue
  t=r.get('target','')
  if t not in latest or r.get('submitted',0)>latest[t].get('submitted',0):latest[t]=r
 return {t for t,r in latest.items() if r.get('rc')==0}
def run(t):
 p=subprocess.run([sys.executable,'-I','-X','utf8','scripts/codex/bank/lambda/lane_client.py',t],cwd=R,capture_output=True,text=True,encoding='utf-8')
 (S/(t.replace('.','_')+'.provider-client.txt')).write_text(p.stdout+'\n'+p.stderr,encoding='utf-8')
 print(t,'rc=',p.returncode,flush=True);return {'target':t,'rc':p.returncode}
pending=set(json.loads((S/'facts-manifest.json').read_text())+json.loads((S/'prices-manifest.json').read_text()))
pending-={'CatalanCore.Uniform.Bank.Lambda.RankFacts.C1S00','CatalanCore.Uniform.Bank.Lambda.RankPrice.C1S00'}
deps={t:set(re.findall(r'^import ([A-Za-z0-9_.]+)',(R/Path(*t.split('.'))).with_suffix('.lean').read_text(),re.M)) for t in pending}
active={};results=[];start=time.monotonic()
with ThreadPoolExecutor(max_workers=2) as pool:
 while pending or active:
  done=accepted();pending-=done
  ready=sorted(t for t in pending if deps[t]<=done and t.rsplit('.',1)[0]+'.C1S00' in done)
  while ready and len(active)<2:
   t=ready.pop(0);pending.remove(t);active[pool.submit(run,t)]=t
  if active:
   finished,_=wait(active,timeout=10,return_when=FIRST_COMPLETED)
   for f in finished:
    active.pop(f);row=f.result();results.append(row)
    if row['rc']:
     pending.add(row['target'])
     (S/'provider-failure.json').write_text(json.dumps({'failed':row,'unlaunched':sorted(pending)},indent=2),encoding='utf-8')
     raise RuntimeError('Provider failure requires source-class audit before continuing')
  elif pending:time.sleep(10)
  if time.monotonic()-start>14400:break
(S/'provider-results.json').write_text(json.dumps({'results':results,'unlaunched':sorted(pending)},indent=2),encoding='utf-8')