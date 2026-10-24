module
public import CatalanCore.Arith.Hybrid.RedInt
public import CatalanCore.Arith.Hybrid.TFullDisplacement
public import CatalanCore.Arith.Hybrid.ChainModelBounds
public import CatalanCore.Arith.Hybrid.ChainPartnerBounds
public import CatalanCore.Arith.Hybrid.ChainResidualBounds
public import CatalanCore.Arith.Hybrid.UniformEntries
public import CatalanCore.Arith.Hybrid.LemmaE.SchurBorder
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

lemma gle0_mul {p : ℕ} [Fact p.Prime] {f g : ℚ[X]} (hf : GLE p 0 f) (hg : GLE p 0 g) :
    GLE p 0 (f * g) := by simpa using hf.mul hg

lemma gle0_of_int1 {p : ℕ} [Fact p.Prime] {f : ℚ[X]} (h : LemmaE.Int1 p f) : GLE p 0 f :=
  (gle_iff_gn p 0 f).2 (by simpa [LemmaE.Int1] using h)

lemma int1_of_gle0 {p : ℕ} [Fact p.Prime] {f : ℚ[X]} (h : GLE p 0 f) : LemmaE.Int1 p f := by
  have := (gle_iff_gn p 0 f).1 h
  simpa [LemmaE.Int1] using this

/-- If `redI f = 0` the polynomial is divisible by `p`, so its Gauss norm is `< 1`. -/
lemma gn_lt_one_of_redI_eq_zero {p : ℕ} [Fact p.Prime] {f : ℚ[X]} (hf : GLE p 0 f)
    (h : redI p f = 0) : gn p f < 1 := by
  obtain ⟨a, rfl⟩ := exists_lift0 p hf
  rw [redI_toQ, phiP_eq_zero_iff] at h
  obtain ⟨b, hb⟩ := h
  have hp0 : (Fact.out : p.Prime).pos = (Fact.out : p.Prime).pos := rfl
  have hCp : toQ p (C ((p:ℕ) : LocRing p)) = C (p:ℚ) := by simp [toQ]
  have : toQ p a = C (p:ℚ) * toQ p b := by rw [hb, map_mul, hCp]
  rw [this, gn_mul, gn_C, padicNorm.padicNorm_p_of_prime]
  have hb1 : gn p (toQ p b) ≤ 1 := by
    have := (gle_iff_gn p 0 (toQ p b)).1 (gle0_toQ p b)
    simpa using this
  have hp1 : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  calc ((p:ℚ)⁻¹ : ℚ) * gn p (toQ p b) ≤ ((p:ℚ)⁻¹ : ℚ) * 1 := by
        push_cast
        exact mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ < 1 := by
        push_cast
        rw [mul_one]; exact inv_lt_one_of_one_lt₀ hp1

/-- A primitive integral polynomial has a nonzero reduction. -/
lemma redI_ne_zero_of_gn_eq_one {p : ℕ} [Fact p.Prime] {f : ℚ[X]} (hf : GLE p 0 f)
    (h1 : gn p f = 1) : redI p f ≠ 0 := fun h =>
  absurd (gn_lt_one_of_redI_eq_zero hf h) (by rw [h1]; exact lt_irrefl _)


namespace ChainModel
open LemmaE
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

/-- The cleared inverse of the actual core block. -/
noncomputable abbrev Nm (Fr : Frame) (p r : ℕ) [Fact p.Prime] {Z : Type} [Fintype Z]
    [DecidableEq Z] (xs ys : Z → ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  Nmat p (fun _ : Fin r => 1) (full Fr p r xs ys).toBlocks₁₁

lemma Nm_apply (i j : Fin r) :
    Nm Fr p r xs ys i j = C ((p:ℚ)^2) * (Q Fr p r xs ys).adjugate i j := by
  rw [Nm, Nmat_const_one]; rfl

lemma C2_eq (z : Z) (i : Fin r) :
    C2 Fr p r xs ys z i = C ((p:ℚ)^2) * (full Fr p r xs ys).toBlocks₂₁ z i := by
  rw [C2_apply, full_C_apply, map_mul]

lemma B2_eq (i : Fin r) (y : Z) :
    B2 Fr p r xs ys i y = C ((p:ℚ)^2) * (full Fr p r xs ys).toBlocks₁₂ i y := by
  rw [B2_apply, full_B_apply, map_mul]

/-- The four one-node moments of the displacement identity (row and column versions). -/
noncomputable def rowB (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) (z : Z) : ℚ[X] :=
  ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i * ∑ k, Nm Fr p r xs ys i k

noncomputable def rowP (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) (z : Z) : ℚ[X] :=
  ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i *
    ∑ k, Nm Fr p r xs ys i k * C (fullPrefix Fr k.val)

noncomputable def colB (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) (y : Z) : ℚ[X] :=
  ∑ j, (∑ k, Nm Fr p r xs ys k j) * (full Fr p r xs ys).toBlocks₁₂ j y

noncomputable def colP (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) (y : Z) : ℚ[X] :=
  ∑ j, (∑ k, C (fullPrefix Fr k.val) * Nm Fr p r xs ys k j) *
    (full Fr p r xs ys).toBlocks₁₂ j y

/-- The four integral moments: `α_z`, `p β_z`, `α'_y`, `p β'_y`. -/
noncomputable def aR (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) (z : Z) : ℚ[X] :=
  (Q Fr p r xs ys).det - rowB Fr p r xs ys z

noncomputable def bR (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) (z : Z) : ℚ[X] :=
  C (p:ℚ) * ((Q Fr p r xs ys).det * C (fullPrefix Fr (xs z)) - rowP Fr p r xs ys z)

noncomputable def aC (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) (y : Z) : ℚ[X] :=
  (Q Fr p r xs ys).det - colB Fr p r xs ys y

noncomputable def bC (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) (y : Z) : ℚ[X] :=
  C (p:ℚ) * ((Q Fr p r xs ys).det * C (fullPrefix Fr (ys y)) - colP Fr p r xs ys y)

/-- **Leading cross-cell identity.**  `g · norm · (y - z) · (p T_zy) = α_z (pβ'_y) - (pβ_z) α'_y`. -/
theorem T_lead_identity (z y : Z) :
    (Q Fr p r xs ys).det * (C Fr.norm * (C (ys y : ℚ) - C (xs z : ℚ))) *
      (C (p:ℚ) * Tscaled (Q Fr p r xs ys).det (full Fr p r xs ys).toBlocks₁₁
        (full Fr p r xs ys).toBlocks₁₂ (full Fr p r xs ys).toBlocks₂₁
        (full Fr p r xs ys).toBlocks₂₂ (Nm Fr p r xs ys) z y) =
      aR Fr p r xs ys z * bC Fr p r xs ys y - bR Fr p r xs ys z * aC Fr p r xs ys y := by
  have H := T_displacement (Fr := Fr) (p := p) (r := r) (xs := xs) (ys := ys) z y
  simp only [aR, bR, aC, bC, rowB, rowP, colB, colP]
  linear_combination (C (p:ℚ)) * H

section Integral
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hx : ∀ z, xs z<N) (hy : ∀ y, ys y<N)
include hL hp hN hr

lemma gle0_det : GLE p 0 (Q Fr p r xs ys).det :=
  gle0_of_int1 (det_int1 (Q_int1 hL hp hN hr))

lemma gle0_adj (i j : Fin r) : GLE p 0 ((Q Fr p r xs ys).adjugate i j) :=
  gle0_of_int1 (adj_int1 (Q_int1 hL hp hN hr) i j)

omit hr in
lemma pPf_mem {a : ℕ} (ha : a < N) : (p:ℚ) * fullPrefix Fr a ∈ LocRing p := by
  have hG := good_interval_delta (p := p) (Fr := Fr) (o := o) (A := 0) hL hN ha
  have he : Ioc 0 a = Icc 1 a := by ext t; simp only [mem_Ioc, mem_Icc]; omega
  rw [he] at hG
  exact hG.mem

lemma gle0_pPf {a : ℕ} (ha : a < N) : GLE p 0 (C ((p:ℚ) * fullPrefix Fr a)) :=
  GLE.C_iff.2 (by simpa using pPf_mem hL hp hN ha)

lemma rowB_eq (z : Z) : rowB Fr p r xs ys z =
    ∑ i, C2 Fr p r xs ys z i * ∑ k, (Q Fr p r xs ys).adjugate i k := by
  unfold rowB
  apply Finset.sum_congr rfl; intro i _
  simp only [Nm_apply, C2_eq, ← Finset.mul_sum]
  ring

lemma bR_eq (z : Z) : bR Fr p r xs ys z =
    (Q Fr p r xs ys).det * C ((p:ℚ) * fullPrefix Fr (xs z)) -
      ∑ i, C2 Fr p r xs ys z i *
        ∑ k, (Q Fr p r xs ys).adjugate i k * C ((p:ℚ) * fullPrefix Fr k.val) := by
  unfold bR rowP
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · rw [map_mul]; ring
  · apply Finset.sum_congr rfl; intro i _
    simp only [Nm_apply, C2_eq, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    ring

lemma colB_eq (y : Z) : colB Fr p r xs ys y =
    ∑ j, (∑ k, (Q Fr p r xs ys).adjugate k j) * B2 Fr p r xs ys j y := by
  unfold colB
  apply Finset.sum_congr rfl; intro j _
  simp only [Nm_apply, B2_eq, ← Finset.mul_sum]
  ring

lemma bC_eq (y : Z) : bC Fr p r xs ys y =
    (Q Fr p r xs ys).det * C ((p:ℚ) * fullPrefix Fr (ys y)) -
      ∑ j, (∑ k, C ((p:ℚ) * fullPrefix Fr k.val) * (Q Fr p r xs ys).adjugate k j) *
        B2 Fr p r xs ys j y := by
  unfold bC colP
  rw [mul_sub]
  congr 1
  · rw [map_mul]; ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    simp only [Nm_apply, B2_eq, map_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _
    ring

lemma int1_pPf {a : ℕ} (ha : a < N) : Int1 p (C ((p:ℚ) * fullPrefix Fr a)) :=
  int1_of_gle0 (gle0_pPf hL hp hN hr ha)

include hx hy

lemma int1_aR (z : Z) : Int1 p (aR Fr p r xs ys z) := by
  rw [aR, rowB_eq hL hp hN hr]
  exact (det_int1 (Q_int1 hL hp hN hr)).sub (Int1.sum fun i _ =>
    (C2_int1 hL hp hN hr hx z i).mul (Int1.sum fun k _ => adj_int1 (Q_int1 hL hp hN hr) i k))

lemma int1_bR (z : Z) : Int1 p (bR Fr p r xs ys z) := by
  rw [bR_eq hL hp hN hr]
  exact ((det_int1 (Q_int1 hL hp hN hr)).mul (int1_pPf hL hp hN hr (hx z))).sub
    (Int1.sum fun i _ => (C2_int1 hL hp hN hr hx z i).mul (Int1.sum fun k _ =>
      (adj_int1 (Q_int1 hL hp hN hr) i k).mul
        (int1_pPf hL hp hN hr (lt_of_lt_of_le k.isLt hr))))

lemma int1_aC (y : Z) : Int1 p (aC Fr p r xs ys y) := by
  unfold aC
  have : colB Fr p r xs ys y = _ := colB_eq hL hp hN hr y
  rw [this]
  exact (det_int1 (Q_int1 hL hp hN hr)).sub (Int1.sum fun j _ =>
    (Int1.sum fun k _ => adj_int1 (Q_int1 hL hp hN hr) k j).mul
      (B2_int1 hL hp hN hr hy j y))

lemma int1_bC (y : Z) : Int1 p (bC Fr p r xs ys y) := by
  rw [bC_eq hL hp hN hr]
  exact ((det_int1 (Q_int1 hL hp hN hr)).mul (int1_pPf hL hp hN hr (hy y))).sub
    (Int1.sum fun j _ => (Int1.sum fun k _ =>
      (int1_pPf hL hp hN hr (lt_of_lt_of_le k.isLt hr)).mul
        (adj_int1 (Q_int1 hL hp hN hr) k j)).mul (B2_int1 hL hp hN hr hy j y))

end Integral


section Lead
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N)
include hL hp hN hr

lemma gn_Nm_le (i j : Fin r) : gn p (Nm Fr p r xs ys i j) ≤ ((p:ℝ)⁻¹)^2 := by
  rw [Nm_apply, gn_mul, show (C ((p:ℚ)^2) : ℚ[X]) = (C (p:ℚ))^2 by rw [map_pow], gn_pow, gn_C,
    padicNorm.padicNorm_p_of_prime]
  have h1 : gn p ((Q Fr p r xs ys).adjugate i j) ≤ 1 := adj_int1 (Q_int1 hL hp hN hr) i j
  have hp0 : (0:ℝ) ≤ ((p:ℝ)⁻¹)^2 := by positivity
  push_cast
  calc ((p:ℝ)⁻¹)^2 * gn p ((Q Fr p r xs ys).adjugate i j) ≤ ((p:ℝ)⁻¹)^2 * 1 :=
        mul_le_mul_of_nonneg_left h1 hp0
    _ = _ := mul_one _

lemma gn_rowsum_le (w : Fin r → ℚ[X]) (hw : ∀ k, Int1 p (w k)) (i : Fin r) :
    gn p (∑ k, Nm Fr p r xs ys i k * w k) ≤ ((p:ℝ)⁻¹)^2 := by
  apply gn_sum_le_const _ _ _ (by positivity)
  intro k _
  rw [gn_mul]
  calc gn p (Nm Fr p r xs ys i k) * gn p (w k) ≤ ((p:ℝ)⁻¹)^2 * 1 :=
        mul_le_mul (gn_Nm_le hL hp hN hr i k) (hw k) (gn_nonneg p _) (by positivity)
    _ = _ := mul_one _

include hk hx in
/-- **Leading moment.**  `h · ∑_i C_zi ∑_k N_ik w_k ≡ g · ∑_m Sr_zm w_m (mod p)` for integral `w`. -/
theorem mom_lead (w : Fin r → ℚ[X]) (hw : ∀ k, Int1 p (w k)) (z : Z) :
    Cng p (h Fr p r xs ys * ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i *
        ∑ k, Nm Fr p r xs ys i k * w k)
      ((Q Fr p r xs ys).det * ∑ m, Sr Fr p r xs ys z m * w m) := by
  have hres := Sr_residual_bound (xs := xs) (ys := ys) hL hp hN hr hk hx
  set A := (full Fr p r xs ys).toBlocks₁₁ with hA
  have hAN : A * Nm Fr p r xs ys = (Q Fr p r xs ys).det • (1 : Matrix (Fin r) (Fin r) ℚ[X]) :=
    AN_eq p (fun _ : Fin r => 1) A
  set rs : Fin r → ℚ[X] := fun i => ∑ k, Nm Fr p r xs ys i k * w k with hrs
  have key : h Fr p r xs ys * ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i * rs i -
      (Q Fr p r xs ys).det * ∑ m, Sr Fr p r xs ys z m * w m =
      ∑ i, ((h Fr p r xs ys • (full Fr p r xs ys).toBlocks₂₁ -
        Sr Fr p r xs ys * A) z i) * rs i := by
    have hAr : ∀ m, ∑ i, A m i * rs i = (Q Fr p r xs ys).det * w m := by
      intro m
      have hAN' : ∀ k, ∑ i, A m i * Nm Fr p r xs ys i k =
          if m = k then (Q Fr p r xs ys).det else 0 := fun k => by
        have := congrFun (congrFun hAN m) k
        simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] using this
      calc ∑ i, A m i * rs i = ∑ i, ∑ k, A m i * Nm Fr p r xs ys i k * w k := by
            apply Finset.sum_congr rfl; intro i _
            simp only [hrs, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
        _ = ∑ k, (∑ i, A m i * Nm Fr p r xs ys i k) * w k := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro k _
            rw [Finset.sum_mul]
        _ = ∑ k, (if m = k then (Q Fr p r xs ys).det else 0) * w k := by
            apply Finset.sum_congr rfl; intro k _; rw [hAN']
        _ = (Q Fr p r xs ys).det * w m := by
            simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e1 : ∑ i, ((Sr Fr p r xs ys * A) z i) * rs i =
        (Q Fr p r xs ys).det * ∑ m, Sr Fr p r xs ys z m * w m := by
      calc ∑ i, ((Sr Fr p r xs ys * A) z i) * rs i
          = ∑ i, ∑ m, Sr Fr p r xs ys z m * (A m i * rs i) := by
            apply Finset.sum_congr rfl; intro i _
            rw [Matrix.mul_apply, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro m _; ring
        _ = ∑ m, Sr Fr p r xs ys z m * ∑ i, A m i * rs i := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro m _
            rw [Finset.mul_sum]
        _ = ∑ m, Sr Fr p r xs ys z m * ((Q Fr p r xs ys).det * w m) := by
            apply Finset.sum_congr rfl; intro m _; rw [hAr]
        _ = _ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro m _; ring
    rw [Finset.mul_sum]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [e1]
    apply congrArg (· - _)
    apply Finset.sum_congr rfl; intro i _; ring
  unfold Cng
  rw [key]
  have hp1 : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0:ℝ) < p := by linarith
  have hb : gn p (∑ i, ((h Fr p r xs ys • (full Fr p r xs ys).toBlocks₂₁ -
      Sr Fr p r xs ys * A) z i) * rs i) ≤ (p:ℝ) * ((p:ℝ)⁻¹)^2 := by
    apply gn_sum_le_const _ _ _ (by positivity)
    intro i _
    rw [gn_mul]
    exact mul_le_mul (hres z i) (gn_rowsum_le hL hp hN hr w hw i) (gn_nonneg p _) hp0.le
  refine lt_of_le_of_lt hb ?_
  have : (p:ℝ) * ((p:ℝ)⁻¹)^2 = (p:ℝ)⁻¹ := by field_simp
  rw [this]
  exact inv_lt_one_of_one_lt₀ hp1

end Lead

section LeadMoments
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N)
include hL hp hN hr hk hx

/-- `h α_z ≡ g (h - ∑_m Sr_zm) (mod p)`. -/
theorem aR_lead (z : Z) :
    Cng p (h Fr p r xs ys * aR Fr p r xs ys z)
      ((Q Fr p r xs ys).det * (h Fr p r xs ys - ∑ m, Sr Fr p r xs ys z m)) := by
  have H := mom_lead (xs := xs) (ys := ys) hL hp hN hr hk hx (fun _ => 1) (fun _ => Int1.one) z
  simp only [mul_one] at H
  have e1 : h Fr p r xs ys * aR Fr p r xs ys z =
      h Fr p r xs ys * (Q Fr p r xs ys).det - h Fr p r xs ys * rowB Fr p r xs ys z := by
    unfold aR; ring
  have e2 : (Q Fr p r xs ys).det * (h Fr p r xs ys - ∑ m, Sr Fr p r xs ys z m) =
      h Fr p r xs ys * (Q Fr p r xs ys).det -
        (Q Fr p r xs ys).det * ∑ m, Sr Fr p r xs ys z m := by ring
  rw [e1, e2]
  exact (Cng.refl _).sub H

/-- `h (pβ_z) ≡ g (h p Pf(x_z) - ∑_m Sr_zm p Pf(m)) (mod p)`. -/
theorem bR_lead (z : Z) :
    Cng p (h Fr p r xs ys * bR Fr p r xs ys z)
      ((Q Fr p r xs ys).det * (h Fr p r xs ys * C ((p:ℚ) * fullPrefix Fr (xs z)) -
        ∑ m, Sr Fr p r xs ys z m * C ((p:ℚ) * fullPrefix Fr m.val))) := by
  have H := mom_lead (xs := xs) (ys := ys) hL hp hN hr hk hx (fun m => C ((p:ℚ) * fullPrefix Fr m.val))
    (fun m => int1_pPf hL hp hN hr (lt_of_lt_of_le m.isLt hr)) z
  have e0 : bR Fr p r xs ys z = (Q Fr p r xs ys).det * C ((p:ℚ) * fullPrefix Fr (xs z)) -
      ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i *
        ∑ k, Nm Fr p r xs ys i k * C ((p:ℚ) * fullPrefix Fr k.val) := by
    unfold bR rowP
    rw [mul_sub, Finset.mul_sum, map_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [map_mul]; ring
  have e1 : h Fr p r xs ys * bR Fr p r xs ys z =
      h Fr p r xs ys * ((Q Fr p r xs ys).det * C ((p:ℚ) * fullPrefix Fr (xs z))) -
      h Fr p r xs ys * ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i *
        ∑ k, Nm Fr p r xs ys i k * C ((p:ℚ) * fullPrefix Fr k.val) := by
    rw [e0]; ring
  have e2 : (Q Fr p r xs ys).det * (h Fr p r xs ys * C ((p:ℚ) * fullPrefix Fr (xs z)) -
        ∑ m, Sr Fr p r xs ys z m * C ((p:ℚ) * fullPrefix Fr m.val)) =
      h Fr p r xs ys * ((Q Fr p r xs ys).det * C ((p:ℚ) * fullPrefix Fr (xs z))) -
        (Q Fr p r xs ys).det * ∑ m, Sr Fr p r xs ys z m * C ((p:ℚ) * fullPrefix Fr m.val) := by
    ring
  rw [e1, e2]
  exact (Cng.refl _).sub H

end LeadMoments

end ChainModel
#print axioms ChainModel.bR_lead
end CatalanCore.Arith.Hybrid
