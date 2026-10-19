# IBoundData.lean: I_rho(sigma) upper bound from scaled-integer log lower bounds; 24 row-chunks of 30
import sys, math; sys.path.insert(0, '.')
from p6mirror import *
OUT = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-thmA/CatalanCore/Cert/SigmaP6/'
def qII(p, q): return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2 + RHO2
def irow(p): return sum(q[2] * logLoS(qII(p, q)) for q in spts)
CH = 30; NCH = (K + CH - 1) // CH
vals = [sum(p[2] * irow(p) for p in spts[r * CH:(r + 1) * CH]) for r in range(NCH)]
tot = sum(vals)
Ival = F(-tot, 2 ** 129)
Ib = F(math.ceil(Ival * 10 ** 5), 10 ** 5)
print(float(Ival), Ib, float(Ib))
HDR = "module

public import CatalanCore.Cert.SigmaP6.%s

@[expose] public section

"
NSP = "namespace CatalanCore.Cert.SigmaP6

open CatalanLambda.Cert

set_option maxRecDepth 100000

"
def w(n, s): open(OUT + n + '.lean', 'w', encoding='utf-8', newline='
').write(s)
w('IBoundDef', HDR % 'Bridge' + "/-! Generated (genI.py): definitions for the I_rho(sigma) upper bound. -/
" + NSP + """def qII (p q : Pt) : ℕ := (p.1 - q.1).natAbs ^ 2 + (p.2.1 - q.2.1).natAbs ^ 2 + 2 ^ 58

def iRow (p : Pt) : List Pt → ℤ
  | [] => 0
  | q :: qs => (q.2.2 : ℤ) * logLoS (qII p q) + iRow p qs

def iTot : List Pt → ℤ
  | [] => 0
  | p :: ps => (p.2.2 : ℤ) * iRow p sigD + iTot ps

def iChunk (r : ℕ) : List Pt := (sigD.drop (30 * r)).take 30

lemma iTot_append (a b : List Pt) : iTot (a ++ b) = iTot a + iTot b := by
  induction a with
  | nil => simp [iTot]
  | cons p ps ih => simp only [List.cons_append, iTot, ih]; ring

end CatalanCore.Cert.SigmaP6
""")
for r, v in enumerate(vals):
    w('IChunk%d' % r, HDR % 'IBoundDef' + "/-! Generated (genI.py): rows %d..%d of the I_rho sum (one kernel cell). -/
" % (30 * r, 30 * r + 29) + NSP + "theorem iChunk_%d : iTot (iChunk %d) = (%d : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaP6
" % (r, r, v))
body = "".join("public import CatalanCore.Cert.SigmaP6.IChunk%d
" % r for r in range(NCH))
s = HDR % 'IBoundDef' + body.replace("public import CatalanCore.Cert.SigmaP6.IBoundDef
", "")
s = s.replace("@[expose] public section

", "") 
s = "module

public import CatalanCore.Cert.SigmaP6.IBoundDef
" + body + "
@[expose] public section

/-! Generated (genI.py): I_rho(sigma) upper bound from %d row-chunks. -/
" % NCH + NSP
s += "theorem sigD_chunks : sigD = %s := by decide +kernel
" % (" ++ ".join("iChunk %d" % r for r in range(NCH)))
s += "
theorem iTot_sigD_val : iTot sigD = (%d : ℤ) := by
  conv_lhs => rw [sigD_chunks]
  simp only [iTot_append]
  rw [%s]
  norm_num
" % (tot, ", ".join("iChunk_%d" % r for r in range(NCH)))
s += "
def IBOUND : ℚ := %d / %d

end CatalanCore.Cert.SigmaP6
" % (Ib.numerator, Ib.denominator)
w('IBoundData', s)
