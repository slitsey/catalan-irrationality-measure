"""Exact sevenths inputs check; independent computation, not Lean acceptance."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True

ROOT = Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea')
SPEC = ROOT / 'outputs/Compatibility programme/bank-specs-2026-10-28'
spec = importlib.util.spec_from_file_location('bank_verifier', SPEC / 'verify_open_math.py')
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
rank = json.loads((SPEC / 'rank-sevenths.json').read_text())
uf = json.loads((SPEC / 'uf-sevenths.json').read_text())
result = dict(rank=verifier.verify_rank(rank), UF=verifier.verify_uf(uf))
expected = {str(a): {str(pc): (a * pow(pc, -1, 7)) % 7 for pc in (1, 3, 5, 9, 11, 13)} for a in range(1, 7)}
assert rank['member_class_to_root'] == uf['member_class_to_root'] == expected
replay = json.loads((SPEC / 'replay-sevenths.json').read_text())
lo = 2 * sum((Q(1, (2*k+1)*3**(2*k+1)) for k in range(25)), Q(0))
hi = lo + Q(2, 51) * Q(1, 3**51) / (1-Q(1, 9))
d = Q(2185487560184413390033, 600000000000000000000)
c = Q(7425954607455103, 1000000000000000)
A, B = Q(replay['UF']['rational']), Q(replay['UF']['log2'])
eta = d - A - B*hi
assert eta > 0
assert c/eta < Q(70993, 20)
assert c/(d-A-B*lo) > Q(17748, 5)  # 3549.6 is below the fixed-rate ratio.
assert d - Q(replay['noUF']['rational']) - Q(replay['noUF']['log2'])*lo < 0
assert hi < Q(693147181, 10**9)
assert c/(d-A-B*Q(693147181, 10**9)) < Q(70993, 20)
result.update(member_class_transport=True, log2_upper=str(hi), eta_lower=str(eta),
              mu_upper=str(c/eta), mu_upper_decimal=float(c/eta), safe_bound='70993/20',
              noUF_eta_negative=True, lean_acceptance=False,
              hashes={name: hashlib.sha256((SPEC/name).read_bytes()).hexdigest() for name in
                      ('rank-sevenths.json', 'uf-sevenths.json', 'replay-sevenths.json', 'verify_open_math.py')})
(Path(__file__).parent / 'input-checks.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
