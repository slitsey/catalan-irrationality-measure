# Sigma.lean (sorted sigma list, X,Y scaled 2^40, masses n/2^32), ConjData.lean
import sys; sys.path.insert(0, '.')
from p6mirror import *
OUT = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-thmA/CatalanCore/Cert/SigmaP6/'
def z(v): return "(%d : ℤ)" % v if v < 0 else str(v)
hdr = "module\n\npublic import CatalanCore.Cert.SigmaP6.Box\n\n@[expose] public section\n\n"
open(OUT + 'Sigma.lean', 'w', encoding='utf-8', newline='\n').write(
    hdr + "/-! Generated (scripts/certgen-p6/gensigma.py): P6 row-D sigma (FK-P6-decay sig_p6_r010_K700w.json), %d points sorted by (X,Y); X,Y scaled 2^40, masses n/2^32. -/\nnamespace CatalanCore.Cert.SigmaP6\n\nset_option maxHeartbeats 4000000 in\ndef sigD : List Pt := [\n" % K
    + ",\n".join("  (%s, %s, %d)" % (z(X), z(Y), n) for X, Y, n in spts) + "]\n\nend CatalanCore.Cert.SigmaP6\n")
idx = {}
for k, p in enumerate(spts): idx[p] = k
cj = [idx[(X, -Y, n)] for X, Y, n in spts]
assert all(cj[cj[k]] == k for k in range(K))
open(OUT + 'ConjData.lean', 'w', encoding='utf-8', newline='\n').write(
    "module\n\npublic import CatalanCore.Cert.SigmaP6.Bridge\n\n@[expose] public section\n\n/-! Generated (gensigma.py): conjugation involution on the sorted sigma list. -/\nnamespace CatalanCore.Cert.SigmaP6\n\ndef conjIdx : List ℕ := [%s]\n\nend CatalanCore.Cert.SigmaP6\n" % ", ".join(map(str, cj)))
print(K)
