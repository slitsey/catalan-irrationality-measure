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
txt = ["module\n\npublic import CatalanCore.Cert.SigmaP6.Bridge\n\n@[expose] public section\n\n/-! Generated (genI.py): I_rho(sigma) upper bound; %d rows in %d chunks of %d. -/\nnamespace CatalanCore.Cert.SigmaP6\n\nopen CatalanLambda.Cert\n\nset_option maxRecDepth 100000\n\n" % (K, NCH, CH)]
txt.append("""def qII (p q : Pt) : ℕ := (p.1 - q.1).natAbs ^ 2 + (p.2.1 - q.2.1).natAbs ^ 2 + 2 ^ 58

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

""")
for r, v in enumerate(vals):
    txt.append("theorem iChunk_%d : iTot (iChunk %d) = (%d : ℤ) := by decide +kernel\n" % (r, r, v))
txt.append("\ntheorem sigD_chunks : sigD = %s := by decide +kernel\n" % (" ++ ".join("iChunk %d" % r for r in range(NCH))))
txt.append("\ntheorem iTot_sigD_val : iTot sigD = (%d : ℤ) := by\n  conv_lhs => rw [sigD_chunks]\n  simp only [iTot_append]\n  rw [%s]\n  norm_num\n" % (tot, ", ".join("iChunk_%d" % r for r in range(NCH))))
txt.append("\ndef IBOUND : ℚ := %d / %d\n\nend CatalanCore.Cert.SigmaP6\n" % (Ib.numerator, Ib.denominator))
open(OUT + 'IBoundData.lean', 'w', encoding='utf-8', newline='\n').write("".join(txt))
