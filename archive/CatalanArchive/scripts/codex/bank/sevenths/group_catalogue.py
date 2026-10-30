"""Keep one declaration per certificate, but compile all types of a root class together."""
from pathlib import Path
import json
R=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform')
B=R/'CatalanCore/Uniform/Bank/Sevenths'
S=R/'scripts/codex/bank/sevenths'
manifest=json.loads((S/'rank-manifest.json').read_text())
header="""import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
"""
classes=sorted(set(e['prime_class'] for e in manifest['certificates']))
for root in classes:
    entries=[e for e in manifest['certificates'] if e['prime_class']==root]
    blocks=[]
    for e in entries:
        text=(B/'RankData'/(e['name']+'.lean')).read_text()
        blocks.append(text[text.index('/-- Source type'):text.rindex('end CatalanCore.Uniform.Bank.Sevenths.RankData')])
    text=header+'\n'.join(blocks)+'\nend CatalanCore.Uniform.Bank.Sevenths.RankData\n'
    (B/'RankData'/f'C{root}.lean').write_text(text,encoding='utf-8')
    blocks=[]
    for e in entries:
        text=(B/'RankPalette'/(e['name']+'.lean')).read_text()
        blocks.append(text[text.index('theorem '+e['name']+'_integral'):text.rindex('end CatalanCore.Uniform.Bank.Sevenths.RankData')])
    ph=f"""import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C{root}
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer
"""
    (B/'RankPalette'/f'C{root}.lean').write_text(ph+'\n'.join(blocks)+'\nend CatalanCore.Uniform.Bank.Sevenths.RankData\n',encoding='utf-8')
(S/'grouped-catalogue.json').write_text(json.dumps(dict(
    source_sha256=manifest['source_sha256'],
    roots=[dict(prime_class=c,data='CatalanCore.Uniform.Bank.Sevenths.RankData.C'+str(c),
                palette='CatalanCore.Uniform.Bank.Sevenths.RankPalette.C'+str(c),
                certificates=[e for e in manifest['certificates'] if e['prime_class']==c])
           for c in classes]),indent=2)+'\n',encoding='utf-8')
print('Prepared',len(classes),'root-class modules covering all',len(manifest['certificates']),'unchanged certificates')
