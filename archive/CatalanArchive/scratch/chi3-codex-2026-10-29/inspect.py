from pathlib import Path
import json,re
r=Path.cwd(); s=r/'scratch/chi3-codex-2026-10-29'; logs=r/'../../outputs/Compatibility programme/lean-plan-2026-10-27/evidence/claude/logs'
rows=[]
for p in logs.glob('*Chi3*Decay-build*.log'):
 t=p.read_text(encoding='utf-8',errors='replace')
 if 'Build completed successfully' in t:
  rows.append(dict(log=str(p.resolve()),built=re.findall(r'.*Built CatalanCore.Uniform.Bank.Chi3.*',t),success=[l for l in t.splitlines() if 'Build completed successfully' in l]))
(s/'baseline-receipts.json').write_text(json.dumps(rows,indent=1),encoding='utf-8')
for d in ('running','queue'):
 items=[json.loads(p.read_text()) for p in (r/'../tools/lanes'/d).glob('*.json')]
 print(d,[(x['target'],x.get('budget')) for x in items])
print('successful baseline receipts',len(rows))
