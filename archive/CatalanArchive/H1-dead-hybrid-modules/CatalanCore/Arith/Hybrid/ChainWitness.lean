module
public import CatalanCore.Arith.Hybrid.ChainWeighted
public import CatalanCore.Arith.Hybrid.WitnessWeight
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open ChainClasses
variable {p r m o k a b : ℕ} [Fact p.Prime] {Fr : Frame}
lemma witness_zero_condition
    (hcut : ∀ x y:ℕ,a≤x→x<b→a≤y→y<b→
      NoCut (Cut p r (Singular p o)) (min (x:ℤ) y) (max (x:ℤ) y))
    (i j : Fin m) (H : witnessTable p r m a b i j=0) :
    NoCut (Cut p r (Singular p o))
      (min ((r+2*i.val:ℕ):ℤ) (r+2*j.val+1))
      (max ((r+2*i.val:ℕ):ℤ) (r+2*j.val+1)) := by
  have HH : a≤r+2*i.val ∧ r+2*i.val<b ∧ a≤r+2*j.val+1 ∧ r+2*j.val+1<b := by
    by_contra hno
    simp only [witnessTable,witnessWeight,if_neg hno] at H
    split_ifs at H <;> omega
  exact hcut _ _ HH.1 HH.2.1 HH.2.2.1 HH.2.2.2
lemma witness_one_condition (i j : Fin m) (H : witnessTable p r m a b i j=1) :
    (r+2*i.val)%p≠(r+2*j.val+1)%p := by
  intro he
  simp only [witnessTable,witnessWeight,he,ite_true] at H
  split_ifs at H <;> omega
theorem witness_original_gle (hL : LamData Fr o) (hp : 5≤p)
    (hN : 4*(r+2*m)<p*p) (hk : (4:ZMod p)*k=o)
    (hcut : ∀ x y:ℕ,a≤x→x<b→a≤y→y<b→
      NoCut (Cut p r (Singular p o)) (min (x:ℤ) y) (max (x:ℤ) y)) :
    GLE p (tropVal (witnessTable p r m a b)+2*r)
      (Rect.FullN Fr (fun i:Fin r=>i.val) (fun i:Fin m=>r+2*i.val)
        (fun j:Fin m=>r+2*j.val+1) (X:ℚ[X])).det := by
  apply original_det_weighted hL hp hN (by omega) hk
    (fun i=>by have:=i.isLt;omega) (fun i=>by have:=i.isLt;omega)
    (fun i=>by omega) (fun i=>by omega) (fun i j=>by omega)
    (witnessTable p r m a b)
  · intro i j;exact witnessWeight_le_two _ _ _ _ _
  · exact witness_zero_condition hcut
  · exact witness_one_condition
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.witness_original_gle
