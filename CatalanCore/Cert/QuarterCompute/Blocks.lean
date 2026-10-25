module
public import CatalanCore.Cert.QuarterCompute.Defs
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute
theorem iRow_append (p : Pt) (xs ys : List Pt) :
    iRow p (xs ++ ys) = iRow p xs + iRow p ys := by
  induction xs with
  | nil => exact (Int.zero_add _).symm
  | cons q qs ih =>
    change (q.2.2 : Int)*logLoS (qII p q)+iRow p (qs++ys) =
      ((q.2.2 : Int)*logLoS (qII p q)+iRow p qs)+iRow p ys
    rw [ih]
    exact (Int.add_assoc _ _ _).symm
end CatalanCore.Cert.QuarterCompute