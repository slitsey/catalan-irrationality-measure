"""Audit/reuse only the old source closure required by new D58 providers."""
import os,sys,re,json,subprocess,collections,time
from pathlib import Path
W=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform');R=W.parent/'catalan-release';E=W.parent.parent/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank/cache-relocation'
seen=set();q=collections.deque(['CatalanMeasure.GenD.Uniform.Bank.Providers532']);old=[]
while q:
 m=q.popleft()
 if m in seen:continue
 seen.add(m);rel=Path(m.replace('.','/')+'.lean');p=W/rel
 if not p.exists():continue
 if (R/rel).exists():old.append(m)
 q.extend(re.findall(r'^(?:public )?(?:meta )?import ([\w.]+)',p.read_text(encoding='utf-8-sig'),re.M))
(E/'required-old-import-closure.json').write_text(json.dumps(sorted(old),indent=2)+'\n')
records=[]
for i in range(0,len(old),35):
 batch=old[i:i+35];p=subprocess.run([sys.executable,str(W/'scripts/uniform-phase1/bank_cache_relocate.py'),*batch],capture_output=True,text=True,encoding='utf8',errors='replace')
 (E/('closure-batch-'+str(i//35)+'.txt')).write_text(p.stdout+p.stderr,encoding='utf8')
 rows=[json.loads(s)for s in p.stdout.splitlines()if s.startswith('{')];records.extend(rows)
 (E/'closure-reuse.json').write_text(json.dumps(dict(required_old_modules=len(old),processed=len(records),receipts=records),indent=2)+'\n')
 print(json.dumps(dict(batch=i//35,processed=len(records),required=len(old),counts=dict(collections.Counter(r['status']for r in rows)))),flush=True)
 if p.returncode:raise RuntimeError('audit batch failed')
print('D58_OLD_CLOSURE_AUDIT_FINISHED',flush=True)

