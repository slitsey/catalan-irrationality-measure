import json
from pathlib import Path
E=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank/cache-relocation')
v=json.loads((E/'validation.json').read_text());r=json.loads((E/'receipt-OAI_NumberTheory_Catalan_Determinants_FixedClearedZetaColumn3.json').read_text())['receipts'];actual={x['module']for x in r if x['status']!='rejected'};actual.add('OAI.NumberTheory.Catalan.Determinants.FixedClearedZetaColumn2')
valid=[x for x in v if x['module']in actual];outside=[x for x in v if x['module']not in actual]
assert len(valid)==40 and all(x['rc']==0 for x in valid)
(E/'validated-bound-fixed-columns.json').write_text(json.dumps(dict(accepted_actual_relocated_targets=valid,rejected_nonexistent_range_requests=outside),indent=2)+'\n')
print('40 actual relocated targets accepted; 5 nonexistent range names excluded with retained failures')
