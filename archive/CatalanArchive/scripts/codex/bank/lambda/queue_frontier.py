"""Queue independent stale leaves together; every child still preflights and adopts."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
import importlib.util,json,sys,threading
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/lambda'
spec=importlib.util.spec_from_file_location('lambda_lane_client',S/'lane_client.py');LC=importlib.util.module_from_spec(spec);spec.loader.exec_module(LC)
sem=threading.BoundedSemaphore(2);original=LC.preflight
def pf(t):
 with sem:return original(t)
LC.preflight=pf
target=sys.argv[1];_,leaves=LC.preflight(target);results=[]
with ThreadPoolExecutor(max_workers=max(1,len(leaves))) as pool:
 fs={pool.submit(LC.build,t):t for t in leaves if t!=target}
 for f in as_completed(fs):
  t=fs[f]
  try:f.result();row={'target':t,'rc':0}
  except Exception as e:row={'target':t,'error':str(e)}
  results.append(row);print(row,flush=True)
(S/(target.replace('.','_')+'.frontier-results.json')).write_text(json.dumps(results,indent=2),encoding='utf-8')