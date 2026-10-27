import re,json,collections
from pathlib import Path
W=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform');R=W.parent/'catalan-release';E=W.parent.parent/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank/cache-relocation'
q=collections.deque(['CatalanMeasure.GenD.Uniform.Bank.ArithmeticCacheAudit']);seen=set();old=[]
while q:
 m=q.popleft()
 if m in seen:continue
 seen.add(m);p=W/(m.replace('.','/')+'.lean')
 if not p.exists():continue
 if (R/p.relative_to(W)).exists():old.append(m)
 q.extend(re.findall(r'^(?:public )?(?:meta )?import ([\w.]+)',p.read_text(encoding='utf-8-sig'),re.M))
(E/'arithmetic-old-import-closure.json').write_text(json.dumps(sorted(old),indent=2)+'\n')
original=E/'source-hash-inputs-758.txt'
if not original.exists():original.write_bytes((E/'source-hash-inputs.txt').read_bytes());(E/'source-hashes-original758.txt').write_bytes((E/'source-hashes.txt').read_bytes())
paths=set((E/'source-hash-inputs.txt').read_text().splitlines());paths.update(str(W/(m.replace('.','/')+'.lean'))for m in old)
(E/'source-hash-inputs.txt').write_text('\n'.join(sorted(paths))+'\n');print('union source files',len(paths),'arithmetic old modules',len(old))
