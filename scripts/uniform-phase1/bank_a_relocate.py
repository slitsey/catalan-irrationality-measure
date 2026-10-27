import os,json,subprocess,sys,collections
from pathlib import Path
W=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform');E=W.parent.parent/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank/cache-relocation'
mods=json.loads((E/'arithmetic-old-import-closure.json').read_text());env=os.environ.copy();env['BANK_CACHE_OWNER']='arithmetic'
p=subprocess.run([sys.executable,str(W/'scripts/uniform-phase1/bank_cache_relocate.py'),*mods],capture_output=True,text=True,encoding='utf8',errors='replace',env=env)
(E/'arithmetic-ownership-audit-console.txt').write_text(p.stdout+p.stderr,encoding='utf8');rows=[json.loads(s)for s in p.stdout.splitlines()if s.startswith('{')]
(E/'arithmetic-ownership-audit.json').write_text(json.dumps(rows,indent=2)+'\n');print(dict(collections.Counter(r['status']for r in rows)),flush=True)
print([(r['module'],r.get('error'))for r in rows if r['status']=='rejected'],flush=True)
raise SystemExit(p.returncode)
