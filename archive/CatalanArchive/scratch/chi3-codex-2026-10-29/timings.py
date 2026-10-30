from pathlib import Path
import json,re,hashlib
r=Path.cwd(); s=r/'scratch/chi3-codex-2026-10-29'; ld=(r/'../../outputs/Compatibility programme/lean-plan-2026-10-27/evidence/claude/logs').resolve()
old=json.loads((s/'old-import-closure.json').read_text()); pre='CatalanCore.Uniform.Bank.Chi3.'
mods=[m for m in old if any(m==pre+x or m.startswith(pre+x+'.') for x in ['Tube','Line','Cap','Energy','Check','Decay']) or m in ['CatalanCore.Uniform.Bank.Chi3New.Energy','CatalanCore.Uniform.Bank.Chi3New.Decay']]
rows=[]
for m in mods:
    files=sorted(ld.glob(m.replace('.','_')+'-build*.log'),key=lambda p:p.stat().st_mtime,reverse=True)
    accepted=None
    for p in files:
        t=p.read_text(encoding='utf-8',errors='replace')
        z=re.search(r'Built '+re.escape(m)+r' \(([^)]+)\)',t)
        if 'Build completed successfully' in t and z:
            seconds=sum(float(a)*{'ms':.001,'s':1,'m':60,'h':3600}[b] for a,b in re.findall(r'([\d.]+)(ms|s|m|h)',z.group(1)))
            accepted=dict(module=m,log=str(p),lean_time=z.group(1),seconds=seconds)
            jp=p.with_suffix('.json')
            if jp.exists(): accepted['wrapper_seconds']=json.loads(jp.read_text()).get('wrapper_wall_seconds')
            break
    rows.append(accepted or dict(module=m,missing=True))
res=dict(modules=len(mods),accepted=sum('seconds' in j for j in rows),sum_lean_module_wall_seconds=sum(j.get('seconds',0) for j in rows),receipts=rows,note='Sum of per-module Lean wall timings, not CPU time or concurrent closure elapsed time; excludes shared generic dependencies.')
(s/'old-closure-timings.json').write_text(json.dumps(res,indent=1))
print({k:v for k,v in res.items() if k!='receipts'})
hashes={}
for p in list((r/'scripts/claude/bank/cover').glob('*.py'))+list((r/'scripts/claude/bank/cover').glob('*.tmpl')):
    hashes[str(p.relative_to(r))]=hashlib.sha256(p.read_bytes()).hexdigest()
(s/'generator-source-hashes.json').write_text(json.dumps(hashes,indent=1))
for p in s.glob('gen*.out'):
    t=p.read_text(encoding='utf-8'); counts={x:len(re.findall('^'+x+' ',t,re.M)) for x in ['T','L','C','PL','E','G','FAIL']}
    print(p.name,p.stat().st_size,counts)
