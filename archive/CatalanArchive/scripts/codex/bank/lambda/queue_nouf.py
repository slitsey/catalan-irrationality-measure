from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import json,subprocess,sys,threading,time
R=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform')
S=R/'scripts/codex/bank/lambda'
stop=threading.Event()
def run(t):
 if stop.is_set():return dict(target=t,state='not-admitted')
 p=subprocess.run([sys.executable,'-I','-X','utf8','scripts/codex/bank/lambda/lane_client.py',t],cwd=R,capture_output=True,text=True,encoding='utf-8')
 path=S/(t.replace('.','_')+'.lane.txt');path.with_suffix('.client.txt').write_text(p.stdout+'\n'+p.stderr,encoding='utf-8')
 print(t,'rc=',p.returncode,flush=True)
 if p.returncode:stop.set()
 return dict(target=t,rc=p.returncode,log=str(path))
if sys.argv[1:] == ['rank-rest']:
 ts=[x['module'] for x in json.loads((S/'rank-manifest.json').read_text())['certificates'] if x['name'] not in ('C1T00','C3T33') and not (S/(x['module'].replace('.','_')+'.lane.txt')).exists()]
else:ts=sys.argv[1:]
with ThreadPoolExecutor(max_workers=3) as pool:
 results=list(pool.map(run,ts))
(S/('queue-result-'+str(int(time.time()))+'.json')).write_text(json.dumps(results,indent=2),encoding='utf-8')
sys.exit(any(x.get('rc',0) for x in results))

