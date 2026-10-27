import sys,subprocess,json,concurrent.futures
from pathlib import Path
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea');W=ROOT/'work/catalan-uniform';E=ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank';R=W/'scripts/uniform-phase0/run_guarded.py'
def check(i):
 t='OAI.NumberTheory.Catalan.Determinants.FixedClearedZetaColumn'+str(i)
 p=subprocess.run([sys.executable,str(R),t,'preflight','1'],capture_output=True,text=True,encoding='utf8',errors='replace')
 (E/'cache-relocation'/('column'+str(i)+'-validation.txt')).write_text(p.stdout+p.stderr)
 r=dict(module=t,rc=p.returncode);print(json.dumps(r),flush=True);return r
with concurrent.futures.ThreadPoolExecutor(max_workers=3)as pool:results=list(pool.map(check,range(2,47)))
(E/'cache-relocation/validation.json').write_text(json.dumps(results,indent=2)+'\n')
assert all(r['rc']==0 for r in results)
