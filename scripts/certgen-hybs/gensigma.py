# Sigma.lean (the 1650-point hybrid list sigH, in pieces, + constants) and ConjData.lean for SigmaHybS.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hsmirror import *
pts = pts_sorted(); K = len(pts); info = data()['info']
assert sum(p[2] for p in pts) == 9 * 2 ** 29
def z(v): return "(%d : ℤ)" % v if v < 0 else str(v)
mp = F(info['MP']); gm = F(info['gmin'])
NL = chr(10)
hdr = "module" + NL + NL + "public import CatalanCore.Cert.SigmaHybS.Box" + NL + NL + "@[expose] public section" + NL + NL
NCHK = 6
sz = (K + NCHK - 1) // NCHK
body = ""
for c in range(NCHK):
    seg = pts[c * sz:(c + 1) * sz]
    body += "set_option maxHeartbeats 4000000 in" + NL + "def sigH%d : List Pt := [" % c + NL + ("," + NL).join("  (%s, %s, %d)" % (z(X), z(Y), n) for X, Y, n in seg) + "]" + NL + NL
body += "def sigH : List Pt := " + " ++ ".join("sigH%d" % c for c in range(NCHK)) + NL + NL
txt = (hdr + "/-! Generated (scripts/certgen-hybs/gensigma.py) from leandata/final4_tight.json: the hybrid measure (1+alpha) sigma, %d points sorted by (X,Y); X,Y scaled 2^40, masses n/2^32, sum 9*2^29 (in %d pieces). -/" % (K, NCHK) + NL +
       "namespace CatalanCore.Cert.SigmaHybS" + NL + NL + body +
       "/-- the certified ray threshold `m'` and line floor `g_min` (Arb values minus the Taylor allowance `tau`). -/" + NL +
       "def MPRAY : ℚ := %d / %d" % (mp.numerator, mp.denominator) + NL + "def GMINS : ℚ := %d / %d" % (gm.numerator, gm.denominator) + NL + NL +
       "end CatalanCore.Cert.SigmaHybS" + NL)
open(OUTD + 'Sigma.lean', 'w', encoding='utf-8', newline=NL).write(txt)
idx = {p: k for k, p in enumerate(pts)}
cj = [idx[(X, -Y, n)] for X, Y, n in pts]
assert all(cj[cj[k]] == k for k in range(K))
open(OUTD + 'ConjData.lean', 'w', encoding='utf-8', newline=NL).write(
    "module" + NL + NL + "public import CatalanCore.Cert.SigmaHybS.Bridge" + NL + NL + "@[expose] public section" + NL + NL +
    "/-! Generated (gensigma.py): conjugation involution on the sorted list. -/" + NL + "namespace CatalanCore.Cert.SigmaHybS" + NL + NL +
    "def conjIdx : List ℕ := [%s]" % ", ".join(map(str, cj)) + NL + NL + "end CatalanCore.Cert.SigmaHybS" + NL)
print(K, 'maxabs x', max(abs(p[0]) for p in pts) / Z, 'y', max(abs(p[1]) for p in pts) / Z, 'min x', min(p[0] for p in pts) / Z, 'max x', max(p[0] for p in pts) / Z)
