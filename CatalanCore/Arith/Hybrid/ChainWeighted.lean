module
public import CatalanCore.Arith.Hybrid.ChainUnordered
public import CatalanCore.Arith.Hybrid.ChainTwoBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}
lemma Q_primitive (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    gn p (Q Fr p r xs ys).det=1 := by
  rw [Q_eq_shift]
  apply prim_det_shift
  intro i j
  exact Mn_square_mem hL hp hN (i.isLt.trans_le hr) (j.isLt.trans_le hr)
theorem delta_gle_weighted (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk : (4:ZMod p)*k=o) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r (Singular p o)) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    ∀ z y,GLE p (W z y) (delta Fr p r xs ys z y) := by
  intro z y
  change GLE p (W z y) (delta Fr p r xs ys z y)
  by_cases hw0 : W z y=0
  · rw [hw0,gle_iff_gn,pow_zero]
    exact delta_int1_distinct hL hp hN hr hk hx hy z y (hxlo z) (hylo y)
      (hzero z y hw0) (hne z y)
  by_cases hw1 : W z y=1
  · rw [hw1]
    exact delta_gle_one_at hL hp hN hr hk hx hy z y (hone z y hw1)
  have hw2 : W z y=2 := by have:=hW z y; omega
  rw [hw2]
  exact delta_gle_two hL hp hN hr hx hy z y

theorem T_entry_weighted (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk : (4:ZMod p)*k=o) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r (Singular p o)) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    ∀ z y,GLE p (W z y) (Tscaled (Q Fr p r xs ys).det
      (full Fr p r xs ys).toBlocks₁₁ (full Fr p r xs ys).toBlocks₁₂
      (full Fr p r xs ys).toBlocks₂₁ (full Fr p r xs ys).toBlocks₂₂
      (Nmat p (fun _:Fin r=>1) (full Fr p r xs ys).toBlocks₁₁) z y) :=
  tcore_vec_T_cleared _ (Q_int1 hL hp hN hr) (Q_primitive hL hp hN hr) _
    (h_primitive hL hp hN hr) (Sr Fr p r xs ys) (Sc Fr p r xs ys) W
    (Sr_residual_bound hL hp hN hr hk hx) (Sc_residual_bound hL hp hN hr hk hy)
    (delta_gle_weighted hL hp hN hr hk hx hy hxlo hylo hne W hW hzero hone)
theorem full_det_weighted (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk : (4:ZMod p)*k=o) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r (Singular p o)) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    GLE p (tropVal W+2*r) (full Fr p r xs ys).det := by
  simpa using tcore_scaled_weighted p (full Fr p r xs ys) (fun _:Fin r=>1)
    (Q_primitive hL hp hN hr) W
    (T_entry_weighted hL hp hN hr hk hx hy hxlo hylo hne W hW hzero hone)
/-- Composition back to the original determinant does not change its denominator budget. -/
theorem original_det_weighted (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk : (4:ZMod p)*k=o) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r (Singular p o)) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    GLE p (tropVal W+2*r) (Rect.FullN Fr (fun i:Fin r=>i.val) xs ys (X:ℚ[X])).det := by
  have H:=full_det_weighted hL hp hN hr hk hx hy hxlo hylo hne W hW hzero hone
  rw [full,det_rescale] at H
  exact GLE.of_rescale H
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.original_det_weighted
