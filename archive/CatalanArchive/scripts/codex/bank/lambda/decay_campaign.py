"""D17's validated full Lambda decay cover, with mandatory preflight and shared admission."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
import importlib.util,json,re,subprocess,sys,threading,time
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/lambda';M='CatalanCore.Uniform.Bank.Lambda.Cover';C=R/Path(*M.split('.'));cache=S/'decay-cover';cache.mkdir(exist_ok=True)
spec=importlib.util.spec_from_file_location('lambda_lane_client',S/'lane_client.py');LC=importlib.util.module_from_spec(spec);spec.loader.exec_module(LC)
sem=threading.BoundedSemaphore(2);original_preflight=LC.preflight
def bounded_preflight(t):
 with sem:return original_preflight(t)
LC.preflight=bounded_preflight

def command(action):
 cmd=[sys.executable,'-I','-X','utf8','scripts/claude/bank/cover/cover.py',action,'Lambda','--mod',M,'--scratch',str(cache)]
 print('D17 stage',action,flush=True)
 subprocess.run(cmd,cwd=R,check=True)

def build_cover():
 modules={}
 for p in C.rglob('*.lean'):
  t='.'.join(p.relative_to(R).with_suffix('').parts)
  deps={x for x in re.findall(r'^(?:public )?import ([A-Za-z0-9_.]+)',p.read_text(encoding='utf-8-sig'),re.M) if x.startswith(M+'.')}
  modules[t]=deps
 pending=set(modules);passed=set();failed={};active={}
 with ThreadPoolExecutor(max_workers=max(1,len(modules))) as pool:
  while pending or active:
   ready=sorted(t for t in pending if modules[t]<=passed)
   for t in ready:
    pending.remove(t);active[pool.submit(LC.build,t)]=t
   if not active:break
   finished,_=wait(active,timeout=30,return_when=FIRST_COMPLETED)
   for f in finished:
    t=active.pop(f)
    try:f.result();passed.add(t);print('Cover accepted',t,flush=True)
    except Exception as e:failed[t]=str(e);print('Cover failed',t,str(e),flush=True)
 result={'accepted':sorted(passed),'failed':failed,'held':sorted(pending),'modules':len(modules)}
 (S/'decay-cover-build-results.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
 if failed or pending:raise RuntimeError('Decay cover has failed or held modules; see decay-cover-build-results.json')
try:
 command('env')
 LC.build(M+'.Env0')
 command('gen')
 command('emit')
 build_cover()
 print('Full D17 Lambda decay cover accepted.',flush=True)
except Exception as e:
 (S/'decay-campaign-failure.json').write_text(json.dumps({'error':str(e),'time':time.time()},indent=2),encoding='utf-8')
 raise
