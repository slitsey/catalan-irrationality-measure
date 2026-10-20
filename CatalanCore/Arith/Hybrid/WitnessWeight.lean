module

public import CatalanCore.Arith.Hybrid.ZoneCount
public import Mathlib.Data.Nat.ModEq

@[expose] public section

/-! # The one-interval zero/one/two weight rule

No maximal-class or optimal-assignment theorem is needed.  In the lower
range, intersect the witness interval with the central region of nodes
having no second representative of their residue in the zone.
-/

namespace CatalanCore.Arith.Hybrid

def witnessWeight (p a b z y : ℕ) : ℕ :=
  if a≤z ∧ z<b ∧ a≤y ∧ y<b then 0 else if z%p=y%p then 2 else 1

def witnessTable (p r m a b : ℕ) (i j : Fin m) : ℕ :=
  witnessWeight p a b (r+2*(i:ℕ)) (r+2*(j:ℕ)+1)

theorem central_noncong {p r N z y : ℕ} (hzlo : N-p≤z) (hzhi : z<r+p)
    (hylo : r≤y) (hyhi : y<N) (hne : z≠y) : z%p≠y%p := by
  intro hm
  have h1 : z≤y := Nat.ModEq.le_of_lt_add hm (by omega)
  have h2 : y≤z := Nat.ModEq.le_of_lt_add hm.symm (by omega)
  omega

theorem witnessWeight_le_two (p a b z y : ℕ) : witnessWeight p a b z y≤2 := by
  unfold witnessWeight
  split_ifs <;> omega

theorem witness_assignment_low {p r m a b : ℕ} (hra : r≤a) (hab : a≤b)
    (hb : b≤r+2*m) (hbp : b≤r+p) (hj : max a (r+2*m-p)≤b) :
    tropVal (witnessTable p r m a b) ≤ 2*m-(b-max a (r+2*m-p)) := by
  apply interval_assignment_bound r m (max a (r+2*m-p)) b
    (hra.trans (le_max_left _ _)) hj hb
  · intro i j; exact witnessWeight_le_two _ _ _ _ _
  · intro i j hi hi' hj hj'
    unfold witnessTable witnessWeight
    rw [if_pos ⟨(le_max_left _ _).trans hi,hi', (le_max_left _ _).trans hj,hj'⟩]
  · intro i j hi hi'
    have hnc := central_noncong ((le_max_right _ _).trans hi) (hi'.trans_le hbp)
      (show r≤r+2*(j:ℕ)+1 by omega)
      (show r+2*(j:ℕ)+1<r+2*m by have := j.isLt; omega)
      (show r+2*(i:ℕ)≠r+2*(j:ℕ)+1 by omega)
    unfold witnessTable witnessWeight
    split_ifs <;> omega
  · intro i j hj hj'
    have hnc := central_noncong ((le_max_right _ _).trans hj) (hj'.trans_le hbp)
      (show r≤r+2*(i:ℕ) by omega)
      (show r+2*(i:ℕ)<r+2*m by have := i.isLt; omega)
      (show r+2*(j:ℕ)+1≠r+2*(i:ℕ) by omega)
    unfold witnessTable witnessWeight
    split_ifs <;> omega

theorem witness_assignment_high {p r m a b : ℕ} (hra : r≤a) (hab : a≤b)
    (hb : b≤r+2*m) (hp : 2*m<p) :
    tropVal (witnessTable p r m a b) ≤ 2*m-(b-a) := by
  have hmax : max a (r+2*m-p)=a := by omega
  have h := witness_assignment_low (p := p) hra hab hb (by omega) (by omega)
  simpa only [hmax] using h

end CatalanCore.Arith.Hybrid
