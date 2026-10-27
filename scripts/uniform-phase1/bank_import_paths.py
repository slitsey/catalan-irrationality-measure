import re,json,hashlib
from pathlib import Path
from collections import deque
W=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform');R=W.parent/'catalan-release';E=W.parent.parent/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank'
start='CatalanMeasure.GenD.Uniform.Bank.Providers532';target='OAI.NumberTheory.Catalan.Determinants.FixedClearedZetaColumn1';q=deque([start]);seen={start:None}
while q:
 m=q.popleft()
 if m==target:break
 p=W/(m.replace('.','/')+'.lean')
 if not p.exists():continue
 for n in re.findall(r'^(?:public )?import ([\w.]+)',p.read_text(encoding='utf-8-sig'),re.M):
  if n not in seen:seen[n]=m;q.append(n)
path=[];m=target
while m is not None:path.append(m);m=seen[m]
path=path[::-1]
files=[]
for rel in ['OAI/NumberTheory/Catalan/Determinants/FixedClearedZetaColumn1.lean','.lake/build/lib/lean/OAI/NumberTheory/Catalan/Determinants/FixedClearedZetaColumn1.olean','.lake/build/lib/lean/OAI/NumberTheory/Catalan/Determinants/FixedClearedZetaColumn1.trace']:
 a,b=W/rel,R/rel;ha=hashlib.sha256(a.read_bytes()).hexdigest();hb=hashlib.sha256(b.read_bytes()).hexdigest();files.append(dict(path=rel,uniform_sha256=ha,release_sha256=hb,identical=ha==hb))
r=dict(shortest_import_path=path,matching_cached_files=files);(E/'import-binding.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
