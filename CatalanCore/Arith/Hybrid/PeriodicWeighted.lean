module
public import CatalanCore.Arith.Hybrid.PeriodicCancellation
public import CatalanCore.Arith.Hybrid.ChainAlgebra
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.Periodic.Model
open LemmaE ChainClasses ChainModel
variable {p r N : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}
lemma A_project_defect (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N)  :
    ∀ i j,gn p ((blockProject (fun i:Fin r=>i.val%p) (full Fr p r xs ys).toBlocks₁₁-
      (full Fr p r xs ys).toBlocks₁₁) i j)≤p := by
  intro i j
  by_cases hij : i.val%p=j.val%p
  · simp [blockProject,blockRect,hij,Matrix.sub_apply,gn_zero]
  · have hne : i≠j := by intro he; subst j; exact hij rfl
    simpa [blockProject,blockRect,hij,Matrix.sub_apply,gn_neg,full_A_apply_ne i j hne] using
      (gle_iff_gn p 1 _).mp (Mn_cross_gle D (i.isLt.trans_le hr) (j.isLt.trans_le hr) hij)

lemma C_project_defect (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N)  (hx : ∀ z,xs z<N) :
    ∀ z i,gn p (((full Fr p r xs ys).toBlocks₂₁-
      blockRect (fun z=>xs z%p) (fun i:Fin r=>i.val%p) (full Fr p r xs ys).toBlocks₂₁) z i)≤p := by
  intro z i
  by_cases hi : xs z%p=i.val%p
  · simp [blockRect,hi,Matrix.sub_apply,gn_zero]
  · simpa [blockRect,hi,Matrix.sub_apply,full_C_apply] using
      (gle_iff_gn p 1 _).mp (Mn_cross_gle D (hx z) (i.isLt.trans_le hr) hi)

lemma B_project_defect (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N)  (hy : ∀ z,ys z<N) :
    ∀ i y,gn p (((full Fr p r xs ys).toBlocks₁₂-
      blockRect (fun i:Fin r=>i.val%p) (fun z=>ys z%p) (full Fr p r xs ys).toBlocks₁₂) i y)≤p := by
  intro i y
  by_cases hi : i.val%p=ys y%p
  · simp [blockRect,hi,Matrix.sub_apply,gn_zero]
  · simpa [blockRect,hi,Matrix.sub_apply,full_B_apply] using
      (gle_iff_gn p 1 _).mp (Mn_cross_gle D (i.isLt.trans_le hr) (hy y) hi)

lemma Sr_residual_bound (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N)  (hx : ∀ z,xs z<N) :
    ∀ z i,gn p ((h Fr p r xs ys • (full Fr p r xs ys).toBlocks₂₁-
      Sr Fr p r xs ys*(full Fr p r xs ys).toBlocks₁₁) z i)≤p :=
  row_residual_bound _ _ _ _ _ _ (le_of_eq (h_primitive D hN hr))
    (Sr_int1 D hN hr hx) Sr_solve p (by positivity)
    (A_project_defect D hN hr) (C_project_defect D hN hr hx)

lemma Sc_residual_bound (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N)  (hy : ∀ z,ys z<N) :
    ∀ i y,gn p ((h Fr p r xs ys • (full Fr p r xs ys).toBlocks₁₂-
      (full Fr p r xs ys).toBlocks₁₁*Sc Fr p r xs ys) i y)≤p :=
  col_residual_bound _ _ _ _ _ _ (le_of_eq (h_primitive D hN hr))
    (Sc_int1 D hN hr hy) Sc_solve p (by positivity)
    (A_project_defect D hN hr) (B_project_defect D hN hr hy)

lemma delta_gle_one_at (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N)
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) (z y : Z) (hxy : xs z%p≠ys y%p) :
    GLE p 1 (delta Fr p r xs ys z y) := by
  apply cleared_delta_gle_at _ _ _ _ _ _ _ (le_of_eq (h_primitive D hN hr))
    (Sr_int1 D hN hr hx) (Sc_int1 D hN hr hy) z y 1
  · rw [full_D_apply]
    exact Mn_cross_gle D (hx z) (hy y) (hxy)
  · intro i hsi
    have hi : xs z%p=i.val%p := by
      by_contra hn
      exact hsi (Sr_support D hN hr z i hn)
    rw [full_B_apply]
    exact Mn_cross_gle D (i.isLt.trans_le hr) (hy y) (by simpa [← hi] using hxy)
  · intro i hsi
    have hi : i.val%p=ys y%p := by
      by_contra hn
      exact hsi (Sc_support D hN hr i y hn)
    rw [full_C_apply]
    exact Mn_cross_gle D (hx z) (i.isLt.trans_le hr) (by simpa [hi] using hxy)
  · intro i j hsi hsj
    have hi : xs z%p=i.val%p := by
      by_contra hn
      exact hsi (Sr_support D hN hr z i hn)
    have hj : j.val%p=ys y%p := by
      by_contra hn
      exact hsj (Sc_support D hN hr j y hn)
    have hij : i.val%p≠j.val%p := by simpa [← hi,hj] using hxy
    rw [full_A_apply_ne i j (by intro he; subst j; exact hij rfl)]
    exact Mn_cross_gle D (i.isLt.trans_le hr) (j.isLt.trans_le hr) hij

lemma A_gle_two (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    ∀ i j,GLE p 2 ((full Fr p r xs ys).toBlocks₁₁ i j) := by
  intro i j
  apply gle_of_scaled_int1
  have H:=Q_int1 (xs:=xs) (ys:=ys) D hN hr i j
  rwa [Q_eq_smul,Matrix.smul_apply,smul_eq_mul] at H

lemma B_gle_two (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,GLE p 2 ((full Fr p r xs ys).toBlocks₁₂ i y) := by
  intro i y
  exact gle_of_scaled_int1 2 _ (B2_int1 D hN hr hy i y)

lemma C_gle_two (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,GLE p 2 ((full Fr p r xs ys).toBlocks₂₁ z i) := by
  intro z i
  exact gle_of_scaled_int1 2 _ (C2_int1 D hN hr hx z i)

lemma D_gle_two (D : PoleData Fr p N) (hN : N<p*p)
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) : ∀ z y,GLE p 2 ((full Fr p r xs ys).toBlocks₂₂ z y) := by
  intro z y
  rw [full_D_apply]
  exact GLE.C_iff.mpr (D.square_mem hN (hx z) (hy y))

lemma delta_gle_two (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) (z y : Z) : GLE p 2 (delta Fr p r xs ys z y) :=
  cleared_delta_gle_at _ _ _ _ _ _ _ (le_of_eq (h_primitive D hN hr))
    (Sr_int1 D hN hr hx) (Sc_int1 D hN hr hy) z y 2
    (D_gle_two D hN hx hy z y)
    (fun i _=>B_gle_two D hN hr hy i y)
    (fun i _=>C_gle_two D hN hr hx z i)
    (fun i j _ _=>A_gle_two D hN hr i j)

theorem delta_int1_noCut (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y)
    (hc : NoCut (Cut p r D.singular)
      (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hd : (ys y : ZMod p)-(xs z : ZMod p)≠0) :
    Int1 p (delta Fr p r xs ys z y) := by
  rcases le_total (xs z) (ys y) with hzy | hyz
  · have hzy' : (xs z:ℤ)≤ys y := by exact_mod_cast hzy
    exact delta_int1_ordered D hN hr hxN hyN z y hz hy hzy
      (by simpa only [min_eq_left hzy',max_eq_right hzy'] using hc) hd
  · have hd' : (xs z : ZMod p)-(ys y : ZMod p)≠0 := by
      intro he
      exact hd (sub_eq_zero.mpr (sub_eq_zero.mp he).symm)
    have hyz' : (ys y:ℤ)≤xs z := by exact_mod_cast hyz
    have H := delta_int1_ordered D hN hr hyN hxN y z hy hz hyz
      (by simpa only [min_eq_right hyz',max_eq_left hyz'] using hc) hd'
    rw [delta_swap] at H
    exact H

theorem delta_int1_distinct (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y)
    (hc : NoCut (Cut p r D.singular)
      (min (xs z:ℤ) (ys y)) (max (xs z:ℤ) (ys y)))
    (hne : xs z≠ys y) : Int1 p (delta Fr p r xs ys z y) := by
  apply delta_int1_noCut D hN hr hxN hyN z y hz hy hc
  intro he
  have H := noCut_mod_ne (Fact.out : p.Prime).pos hne hc
  exact H ((ZMod.natCast_eq_natCast_iff' _ _ _).mp (sub_eq_zero.mp he).symm)

lemma Q_primitive (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    gn p (Q Fr p r xs ys).det=1 := by
  rw [Q_eq_shift]
  apply prim_det_shift
  intro i j
  exact D.square_mem hN (i.isLt.trans_le hr) (j.isLt.trans_le hr)

theorem delta_gle_weighted (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r D.singular) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    ∀ z y,GLE p (W z y) (delta Fr p r xs ys z y) := by
  intro z y
  change GLE p (W z y) (delta Fr p r xs ys z y)
  by_cases hw0 : W z y=0
  · rw [hw0,gle_iff_gn,pow_zero]
    exact delta_int1_distinct D hN hr hx hy z y (hxlo z) (hylo y)
      (hzero z y hw0) (hne z y)
  by_cases hw1 : W z y=1
  · rw [hw1]
    exact delta_gle_one_at D hN hr hx hy z y (hone z y hw1)
  have hw2 : W z y=2 := by have:=hW z y; omega
  rw [hw2]
  exact delta_gle_two D hN hr hx hy z y

theorem T_entry_weighted (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r D.singular) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    ∀ z y,GLE p (W z y) (Tscaled (Q Fr p r xs ys).det
      (full Fr p r xs ys).toBlocks₁₁ (full Fr p r xs ys).toBlocks₁₂
      (full Fr p r xs ys).toBlocks₂₁ (full Fr p r xs ys).toBlocks₂₂
      (Nmat p (fun _:Fin r=>1) (full Fr p r xs ys).toBlocks₁₁) z y) :=
  tcore_vec_T_cleared _ (Q_int1 D hN hr) (Q_primitive D hN hr) _
    (h_primitive D hN hr) (Sr Fr p r xs ys) (Sc Fr p r xs ys) W
    (Sr_residual_bound D hN hr hx) (Sc_residual_bound D hN hr hy)
    (delta_gle_weighted D hN hr hx hy hxlo hylo hne W hW hzero hone)

theorem full_det_weighted (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r D.singular) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    GLE p (tropVal W+2*r) (full Fr p r xs ys).det := by
  simpa using tcore_scaled_weighted p (full Fr p r xs ys) (fun _:Fin r=>1)
    (Q_primitive D hN hr) W
    (T_entry_weighted D hN hr hx hy hxlo hylo hne W hW hzero hone)

theorem original_det_weighted (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r D.singular) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    GLE p (tropVal W+2*r) (Rect.FullN Fr (fun i:Fin r=>i.val) xs ys (X:ℚ[X])).det := by
  have H:=full_det_weighted D hN hr hx hy hxlo hylo hne W hW hzero hone
  rw [full,det_rescale] at H
  exact GLE.of_rescale H
end CatalanCore.Arith.Hybrid.Periodic.Model
