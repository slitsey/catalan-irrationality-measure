"""Deploy the memory-qualified root-class catalogue; preserve all superseded sources."""
from pathlib import Path
import json,re,subprocess,time
R=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform').resolve()
B=R/'CatalanCore/Uniform/Bank/Sevenths';S=R/'scripts/codex/bank/sevenths'
L=R.parent/'tools/lanes'
old=re.compile(r'^CatalanCore\.Uniform\.Bank\.Sevenths\.(?:RankData|RankPalette)\.C\d+T\d+$')
last=None
while True:
    active=[]
    for folder in ('queue','running'):
        for p in (L/folder).glob('*.json'):
            try:
                target=json.loads(p.read_text(encoding='utf-8-sig')).get('target','')
                if old.match(target) or target.startswith('CatalanCore.Uniform.Bank.Sevenths.RankFibre.'):
                    active.append(target)
            except (ValueError,OSError):
                pass
    if not active: break
    if active!=last:
        print('Draining already admitted old-layout work:',active,flush=True);last=active
    time.sleep(3)
# Check that no other lane imports an individual file being superseded.
q=subprocess.run(['rg','-l',r'^import CatalanCore\.Uniform\.Bank\.Sevenths\.Rank(?:Data|Palette)\.C\d+T\d+',
                  'CatalanCore','CatalanFrames','CatalanMeasure'],cwd=R,capture_output=True,text=True)
for line in q.stdout.splitlines():
    p=(R/line).resolve()
    if not p.is_relative_to(B):
        raise RuntimeError('external live importer requires coordinator reconciliation: '+str(p))
pattern=re.compile(r'(?m)^import (CatalanCore\.Uniform\.Bank\.Sevenths\.Rank(?:Data|Palette)\.C\d+)T\d+[ \t]*$')
for p in B.rglob('*.lean'):
    if p.parent.name in ('RankData','RankPalette') and re.fullmatch(r'C\d+T\d+',p.stem):
        continue
    text=p.read_text(encoding='utf-8-sig')
    updated=pattern.sub(r'import \1',text)
    lines=[];seen=set()
    for line in updated.splitlines():
        if line.startswith('import '):
            if line in seen: continue
            seen.add(line)
        lines.append(line)
    updated='\n'.join(lines)+'\n'
    if updated!=text:
        p.write_text(updated,encoding='utf-8')
roots=json.loads((S/'grouped-catalogue.json').read_text())['roots']
for kind in ('RankData','RankPalette'):
    (B/kind/'Audit.lean').write_text(
        '\n'.join('import CatalanCore.Uniform.Bank.Sevenths.'+kind+'.C'+str(r['prime_class']) for r in roots)+'\n',
        encoding='utf-8')
archive=(R/'archive/CatalanArchive').resolve()
moved=[]
for kind in ('RankData','RankPalette'):
    for src in (B/kind).glob('C*T*.lean'):
        if not re.fullmatch(r'C\d+T\d+',src.stem): continue
        dst=(archive/src.relative_to(R)).resolve()
        assert src.resolve().is_relative_to(B) and dst.is_relative_to(archive)
        if dst.exists(): raise RuntimeError('archive already exists: '+str(dst))
        dst.parent.mkdir(parents=True,exist_ok=True)
        src.replace(dst);moved.append(str(dst.relative_to(R)))
# Freeze a reproducible emitter which reads the archived exact declarations.
group=(S/'group_catalogue.py').read_text(encoding='utf-8-sig')
group=group.replace("S=R/'scripts/codex/bank/sevenths'",
                    "S=R/'scripts/codex/bank/sevenths'\nA=R/'archive/CatalanArchive/CatalanCore/Uniform/Bank/Sevenths'")
group=group.replace("text=(B/'RankData'","text=(A/'RankData'").replace("text=(B/'RankPalette'","text=(A/'RankPalette'")
(S/'prepare_rank.py').write_text(group,encoding='utf-8')
src=S/'group_catalogue.py';dst=archive/src.relative_to(R)
assert dst.resolve().is_relative_to(archive)
dst.parent.mkdir(parents=True,exist_ok=True);src.replace(dst)
# The old per-file emitters must not recreate superseded files.
wrapper="""from pathlib import Path
p=Path(__file__).with_name('prepare_rank.py')
exec(compile(p.read_text(encoding='utf-8'),str(p),'exec'),{'__file__':str(p)})
"""
(S/'generate_palette.py').write_text(wrapper,encoding='utf-8')
p=S/'prepare_content.py';text=p.read_text(encoding='utf-8-sig')
start=text.index('# Reuse the existing certificate emitter')
end=text.index("s = (ROOT/'CatalanCore/Uniform/Bank/Lambda/PolePalette.lean')",start)
text=text[:start]+wrapper+'\n'+text[end:]
p.write_text(text,encoding='utf-8')
p=S/'build_catalogue.py';text=p.read_text(encoding='utf-8-sig')
text=text.replace("manifest = json.loads((HERE/'rank-manifest.json').read_text())['certificates']",
"""manifest = [dict(module=r['data']) for r in
            json.loads((HERE/'grouped-catalogue.json').read_text())['roots']]""")
text=text.replace('ALL_240_DATA_AND_PALETTE_CERTIFICATES_ACCEPTED',
                  'ALL_240_DATA_AND_PALETTE_CERTIFICATES_ACCEPTED_IN_SIX_ROOT_CLASSES')
p.write_text(text,encoding='utf-8')
# Update the physical-fibre emitter as well as its currently emitted consumers.
p=S/'generate_fibre.py';text=p.read_text(encoding='utf-8-sig')
text=text.replace("names=sorted({tnames[v['type_id']] for v in cell['runs']})",
                  "names=[f'C{case[\"prime_class\"]}']")
p.write_text(text,encoding='utf-8')
(S/'grouped-deployment.json').write_text(json.dumps(dict(
    qualified_data_peak_bytes=1895387136,qualified_palette_peak_bytes=1832206336,
    moved=moved,certificate_count=240,root_classes=len(roots)),indent=2)+'\n',encoding='utf-8')
print('Deployed six root classes; archived',len(moved),'individual source files',flush=True)
