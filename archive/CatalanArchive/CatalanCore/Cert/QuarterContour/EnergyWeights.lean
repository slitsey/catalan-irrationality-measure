module
public import CatalanCore.Cert.QuarterContour.EnergyIndexed
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.EnergyIndexed
open CatalanCore.Cert.SigmaP6

/-- Check a local mass slice once, rather than repeatedly traversing the full witness. -/
lemma mass_from_slice (all : List Pt) (start n : ℕ) (weights : List ℕ)
    (h : ((all.drop start).take n).map (fun p => p.2.2) = weights)
    (k : ℕ) (hk : k < n) :
    (pointAt all (start+k)).2.2 = weights.getD k 0 := by
  rw [← h]
  change _ = (((all.drop start).take n).map (fun p => p.2.2)).getD k (((0,0,0) : Pt).2.2)

  unfold pointAt
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_take_of_lt hk,List.getElem?_drop]
  cases all[start+k]? <;> rfl
end CatalanCore.Cert.QuarterContour.EnergyIndexed
#print axioms CatalanCore.Cert.QuarterContour.EnergyIndexed.mass_from_slice