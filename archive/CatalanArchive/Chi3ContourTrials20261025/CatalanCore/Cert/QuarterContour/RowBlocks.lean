module
public import CatalanCore.Cert.QuarterContour.EnergyFold
@[expose] public section
namespace CatalanCore.Cert.QuarterContour
open CatalanCore.Cert.SigmaP6
lemma iRow_append (p : Pt) (xs ys : List Pt) :
    iRow p (xs ++ ys) = iRow p xs + iRow p ys := by
  induction xs with
  | nil => simp [iRow]
  | cons q qs ih => simp only [List.cons_append, iRow, ih]; omega
end CatalanCore.Cert.QuarterContour