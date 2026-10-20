module
public import CatalanCore.Arith.Hybrid.ChainSameClass
public import CatalanCore.Arith.Hybrid.ChainSymmetry
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainClasses
lemma noCut_mod_ne_ordered {p r a b : ℕ} {sing : ℤ→Prop} (hp : 0<p) (hab : a<b)
    (hc : NoCut (Cut p r sing) a b) : a%p≠b%p := by
  intro he
  have hstep : a+p≤b := Nat.ModEq.add_le_of_lt he hab
  have hmod := Nat.mod_add_div a p
  have hlt := Nat.mod_lt a hp
  let t := p*(a/p+1)
  have hat : a<t := by dsimp [t]; nlinarith
  have htb : t≤b := by dsimp [t]; nlinarith [Nat.zero_le (a%p)]
  apply hc t (by exact_mod_cast hat) (by exact_mod_cast htb)
  exact Or.inr (Or.inl ⟨(a/p+1:ℕ),by dsimp [t]; push_cast; ring⟩)

lemma noCut_mod_ne {p r a b : ℕ} {sing : ℤ→Prop} (hp : 0<p) (hne : a≠b)
    (hc : NoCut (Cut p r sing) (min (a:ℤ) b) (max (a:ℤ) b)) : a%p≠b%p := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · apply noCut_mod_ne_ordered hp hab
    have hle : (a:ℤ)≤b := by exact_mod_cast hab.le
    simpa only [min_eq_left hle,max_eq_right hle] using hc
  · apply Ne.symm
    apply noCut_mod_ne_ordered hp hba
    have hle : (b:ℤ)≤a := by exact_mod_cast hba.le
    simpa only [min_eq_right hle,max_eq_left hle] using hc
end CatalanCore.Arith.Hybrid.ChainClasses
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}
/-- The same-class cleared difference is integral in either node order. -/
theorem delta_int1_noCut (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk4 : (4:ZMod p)*k=o) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y)
    (hc : NoCut (Cut p r (Singular p o))
      (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hd : (ys y : ZMod p)-(xs z : ZMod p)≠0) :
    Int1 p (delta Fr p r xs ys z y) := by
  rcases le_total (xs z) (ys y) with hzy | hyz
  · have hzy' : (xs z:ℤ)≤ys y := by exact_mod_cast hzy
    exact delta_int1_ordered hL hp5 hN hr hk4 hxN hyN z y hz hy hzy
      (by simpa only [min_eq_left hzy',max_eq_right hzy'] using hc) hd
  · have hd' : (xs z : ZMod p)-(ys y : ZMod p)≠0 := by
      intro he
      exact hd (sub_eq_zero.mpr (sub_eq_zero.mp he).symm)
    have hyz' : (ys y:ℤ)≤xs z := by exact_mod_cast hyz
    have H := delta_int1_ordered hL hp5 hN hr hk4 hyN hxN y z hy hz hyz
      (by simpa only [min_eq_right hyz',max_eq_left hyz'] using hc) hd'
    rw [delta_swap] at H
    exact H

theorem delta_int1_distinct (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk4 : (4:ZMod p)*k=o) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y)
    (hc : NoCut (Cut p r (Singular p o))
      (min (xs z:ℤ) (ys y)) (max (xs z:ℤ) (ys y)))
    (hne : xs z≠ys y) : Int1 p (delta Fr p r xs ys z y) := by
  apply delta_int1_noCut hL hp5 hN hr hk4 hxN hyN z y hz hy hc
  intro he
  have H := noCut_mod_ne (Fact.out : p.Prime).pos hne hc
  exact H ((ZMod.natCast_eq_natCast_iff' _ _ _).mp (sub_eq_zero.mp he).symm)
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.delta_int1_noCut
#print axioms CatalanCore.Arith.Hybrid.ChainModel.delta_int1_distinct
