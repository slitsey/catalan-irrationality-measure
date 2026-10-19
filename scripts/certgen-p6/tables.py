# Tables TUP/TLO/ALO read from the legacy Lean source (identical literals), instead of recomputing.
import re
S = 2 ** 64; JM = 208
_t = open('C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-repo/CatalanLambda/Cert/Tables.lean').read()
def _get(n): return int(re.search(r'def %s : Nat := (\d+)' % n, _t).group(1))
def _unpack(v, k): return [(v >> (64 * i)) & (S - 1) for i in range(k)]
tup = _unpack(_get('TUP'), 257); tlo = _unpack(_get('TLO'), 257); alo = _unpack(_get('ALO'), JM + 1)
