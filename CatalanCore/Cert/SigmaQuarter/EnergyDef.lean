module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaP6.IBound

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def energyTot : List Pt → ℤ
  | [] => 0
  | p :: ps => (p.2.2 : ℤ) * iRow p pts + energyTot ps

def energyChunk (r : ℕ) : List Pt := (pts.drop (10 * r)).take 10

lemma energyTot_append (a b : List Pt) : energyTot (a ++ b) = energyTot a + energyTot b := by
  induction a with
  | nil => simp [energyTot]
  | cons p ps ih => simp only [List.cons_append, energyTot, ih]; ring

end CatalanCore.Cert.SigmaQuarter
