import json
from pathlib import Path
W=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform');E=W.parent.parent/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank/cache-relocation';mods=json.loads((E/'required-old-import-closure.json').read_text());(E/'source-hash-inputs.txt').write_text('\n'.join(str(W/(m.replace('.','/')+'.lean'))for m in mods)+'\n',encoding='utf8')
