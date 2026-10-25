module
public import CatalanCore.Cert.QuarterContour.EnergyFold
public import CatalanCore.Cert.QuarterCompute.Bridge
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.EnergyIndexed
open CatalanCore.Cert.SigmaP6

/-- The weighted contribution of one already certified row. -/
def weightedRow (all : List Pt) (r : ℕ) : ℤ :=
  ((pointAt all r).2.2 : ℤ)*iRow (pointAt all r) all

def indexSum (all : List Pt) (rs : List ℕ) : ℤ := (rs.map (weightedRow all)).sum

lemma indexSum_append (all : List Pt) (xs ys : List ℕ) :
    indexSum all (xs++ys) = indexSum all xs+indexSum all ys := by
  simp only [indexSum,List.map_append,List.sum_append]

lemma indexSum_flatten (all : List Pt) (blocks : List (List ℕ)) :
    indexSum all blocks.flatten = (blocks.map (indexSum all)).sum := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatten_cons,indexSum_append,ih,List.map_cons,List.sum_cons]

lemma energyTotal_map_indices (all : List Pt) (rs : List ℕ) :
    energyTotal all (rs.map (pointAt all)) = indexSum all rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,energyTotal,ih,indexSum,List.map_cons,List.sum_cons,weightedRow]

lemma points_range (all : List Pt) : (List.range all.length).map (pointAt all) = all := by
  apply List.ext_getElem
  · simp
  · intro n hn hm
    simp only [List.getElem_map,List.getElem_range]
    unfold pointAt
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hm]
    rfl

/-- Index arithmetic may replace the outer list traversal without touching logarithmic rows. -/
theorem energyTotal_indexed (all : List Pt) :
    energyTotal all all = indexSum all (List.range all.length) := by
  calc
    energyTotal all all = energyTotal all ((List.range all.length).map (pointAt all)) :=
      congrArg (energyTotal all) (points_range all).symm
    _ = indexSum all (List.range all.length) := energyTotal_map_indices all _
end CatalanCore.Cert.QuarterContour.EnergyIndexed
#print axioms CatalanCore.Cert.QuarterContour.EnergyIndexed.energyTotal_indexed