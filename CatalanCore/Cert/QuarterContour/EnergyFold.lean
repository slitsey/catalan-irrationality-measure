module
public import CatalanCore.Cert.QuarterContour.Energy
@[expose] public section
namespace CatalanCore.Cert.QuarterContour
open CatalanCore.Cert.SigmaP6

lemma energyTotal_append (all xs ys : List Pt) :
    energyTotal all (xs ++ ys) = energyTotal all xs + energyTotal all ys := by
  induction xs with
  | nil => simp [energyTotal]
  | cons p ps ih => simp only [List.cons_append, energyTotal, ih]; omega

/-- Replace already certified rows before evaluating any weighted sums. -/
lemma energyTotal_of_rows (all rows : List Pt) (value : Pt → ℤ)
    (h : ∀ p ∈ rows, iRow p all = value p) :
    energyTotal all rows = (rows.map (fun p => (p.2.2 : ℤ) * value p)).sum := by
  induction rows with
  | nil => simp [energyTotal]
  | cons p ps ih =>
    rw [energyTotal, h p (by simp), ih (by intro q hq; exact h q (by simp [hq]))]
    rfl

/-- Finite blocks may be certified independently and combined without unfolding rows. -/
lemma energyTotal_flatten (all : List Pt) (blocks : List (List Pt)) :
    energyTotal all blocks.flatten = (blocks.map (energyTotal all)).sum := by
  induction blocks with
  | nil => simp [energyTotal]
  | cons b bs ih => simp only [List.flatten_cons, energyTotal_append, ih, List.map_cons, List.sum_cons]

end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.energyTotal_of_rows
#print axioms CatalanCore.Cert.QuarterContour.energyTotal_flatten