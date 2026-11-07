module

public import CatalanMeasure.GenD.Signed.PickDet
public import CatalanMeasure.GenD.Analytic.MarkedSheet
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import CatalanMeasure.GenD.Signed.RatioIdentity

/-!
# The real-place determinant at the level of Gram matrices (A8, theorem layer)

PROOF-C Theorem C.3 is stated for the operator `L = I + T` on the model space `K_B`.  The
Lean data are the Gram matrices in the Szegő-kernel basis `k_a`: with `K = [1/(1 - x_a x_b)]`
and `F(w) = K + diag(D_-, w D_+)` (`D_± = diag(B'(x_a) x_a^e)` on the weight-1 / weight-`w`
nodes) one has `det L(w) = det F(w) / det K`.  A Gram matrix is not in an orthonormal frame, so
`abs_det_fromBlocks_le_eleven` cannot be applied verbatim.  This file proves the metric-aware form:

* `norm_det_le_of_loewner_gram`: `-rSg ≤ M ≤ rSg` gives `‖det M‖ ≤ r^n det Sg` (Cholesky of `Sg`);
* `norm_det_schur_le`: the Schur-complement form of C.3, `‖det (S₁ - 6 D)‖ ≤ (2+6τ)^n det Sg`;
* `det_gram_blocks`: `det F(w) = det(K₋₋ + D₋) · det(S₀ + w D₊)` and `det K = det K₋₋ · det Sg`;
* `schur_form_*`: the quadratic-form facts turning the Gram-level hypotheses
  (`F(1) ≥ 0`, `F(1) ≤ 2K`, `±D₊ ≤ τ K` on all vectors, which is exactly the shape delivered by
  `lemmaT_of_class`) into the Schur-complement hypotheses;
* `norm_det_gram_le`: the combined statement
  `‖det F(-5)‖ ≤ (2+6τ)^q · det(K₋₋ + D₋) / det K₋₋ · det K`.

The real-place layer (RP lane) on top of these:

* `kC_mul_inv_mul` (Cauchy-inverse identity `K · diag(1/B') · K = diag(B')`), `pick_F_nonneg`
  and `pick_F_le_two_K` (`F(1) ≥ 0`, `F(1) ≤ 2K`, from Pick and the identity), `negBlock_posDef`
  (strictness of `K₁₁ + D₋`, with the positivity inside `log_route_two`: `route_ratio_pos`);
* `posSemidef_map_ofReal`, `lemmaT_sum_form`, `lemmaT_loewner_complex`, `exists_sign_split` (the
  real-to-complex transfer of `lemmaT_of_class` and the reindexing `Fin n ≃ Fin k ⊕ Fin q`);
* `lemma51_weighted` and `abs_det_laurent_eq` (the Laurent-to-Gram determinant identity with signed
  weights on all nodes), `norm_det_gram_le_full` and `abs_det_laurent_le`
  (`|det Laurent| ≤ 11^q ∏|x|^{g-(n-1)} |V(x)| exp (logRatioZ (q-g) xn gp)`);
* `markedSheetCore_zero_le`, `SignedClassBound` and `signedSecondSheet` (`SignedSecondSheetCore` for
  free points, `α₁ = 0`; the non-class branch uses `SheetCopy`).
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

section Loewner

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `-rSg ≤ M ≤ rSg` with `Sg` positive definite gives `‖det M‖ ≤ r ^ n · det Sg`. -/
theorem norm_det_le_of_loewner_gram {Sg M : Matrix n n ℂ} (hSg : Sg.PosDef)
    (hM : M.IsHermitian) {r : ℝ}
    (h1 : ((r : ℂ) • Sg - M).PosSemidef) (h2 : ((r : ℂ) • Sg + M).PosSemidef) :
    ‖M.det‖ ≤ r ^ Fintype.card n * Sg.det.re := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hSg.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hR
  have hdetSg : Sg.det = star R.det * R.det := by
    rw [hR, det_mul, det_conjTranspose]
  have hpos : 0 < Sg.det := hSg.det_pos
  have hRu : IsUnit R.det := by
    refine isUnit_iff_ne_zero.mpr fun h => ?_
    rw [h] at hdetSg
    simp at hdetSg
    exact hpos.ne' hdetSg
  have hRu' : IsUnit R := (isUnit_iff_isUnit_det R).mpr hRu
  set Ri : Matrix n n ℂ := R⁻¹ with hRi
  have hRRi : R * Ri = 1 := Matrix.mul_nonsing_inv _ hRu
  have hRiR : Ri * R = 1 := Matrix.nonsing_inv_mul _ hRu
  set M' : Matrix n n ℂ := Riᴴ * M * Ri with hM'
  have hRiH : Rᴴ * Riᴴ = 1 := by rw [← conjTranspose_mul, hRiR]; simp
  have hRRiH : Riᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRRi]; simp
  have hM'h : M'.IsHermitian := by
    show M'ᴴ = M'
    simp [hM', conjTranspose_mul, hM.eq, Matrix.mul_assoc]
  have hSg1 : Riᴴ * Sg * Ri = 1 := by
    rw [hR]
    calc Riᴴ * (Rᴴ * R) * Ri = (Riᴴ * Rᴴ) * (R * Ri) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hRRiH, hRRi, Matrix.one_mul]
  have e1 : (r : ℂ) • (1 : Matrix n n ℂ) - M' = Riᴴ * ((r : ℂ) • Sg - M) * Ri := by
    simp only [hM', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hSg1]
  have e2 : (r : ℂ) • (1 : Matrix n n ℂ) + M' = Riᴴ * ((r : ℂ) • Sg + M) * Ri := by
    simp only [hM', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hSg1]
  have hb := CatalanMeasure.GenD.Signed.norm_det_le_of_loewner hM'h
    (by rw [e1]; exact h1.conjTranspose_mul_mul_same Ri)
    (by rw [e2]; exact h2.conjTranspose_mul_mul_same Ri)
  have hMeq : M = Rᴴ * M' * R := by
    have : Rᴴ * M' * R = (Rᴴ * Riᴴ) * M * (Ri * R) := by
      simp only [hM', Matrix.mul_assoc]
    rw [this, hRiH, hRiR]; simp
  have hnorm : ‖M.det‖ = ‖M'.det‖ * Sg.det.re := by
    have hSgre : Sg.det.re = ‖R.det‖ ^ 2 := by
      rw [hdetSg]
      have : star R.det * R.det = ((Complex.normSq R.det : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self]; rfl
      rw [this, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hSgre]
    conv_lhs => rw [hMeq]
    rw [det_mul, det_mul, det_conjTranspose, norm_mul, norm_mul, norm_star]
    ring
  have hre : 0 ≤ Sg.det.re := (Complex.lt_def.mp hpos).1.le
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right hb hre

end Loewner

section SchurLevel

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Theorem C.3 in the metric of the Gram matrix `Sg` (Schur complement of the Cauchy matrix on
the weight-`w` nodes): `0 ≤ S₁ ≤ 2 Sg`, `-τ Sg ≤ D ≤ τ Sg` give `‖det (S₁ - 6 D)‖ ≤ (2+6τ)^n det Sg`. -/
theorem norm_det_schur_le {Sg S1 Dp : Matrix n n ℂ} (hSg : Sg.PosDef)
    (hS1 : S1.PosSemidef) (hDp : Dp.IsHermitian) {τ : ℝ} (hτ : 0 ≤ τ)
    (hb : ((2 : ℂ) • Sg - S1).PosSemidef)
    (hc1 : ((τ : ℂ) • Sg - Dp).PosSemidef) (hc2 : ((τ : ℂ) • Sg + Dp).PosSemidef) :
    ‖(S1 - (6 : ℂ) • Dp).det‖ ≤ (2 + 6 * τ) ^ Fintype.card n * Sg.det.re := by
  have hτc : (0 : ℂ) ≤ (τ : ℂ) := Complex.zero_le_real.mpr hτ
  have h6 : (0 : ℂ) ≤ 6 := by norm_num
  have hM : (S1 - (6 : ℂ) • Dp).IsHermitian := hS1.1.sub (hDp.smul (by
    rw [IsSelfAdjoint, Complex.star_def]; simp [Complex.conj_ofNat]))
  refine norm_det_le_of_loewner_gram hSg hM ?_ ?_
  · have : (((2 + 6 * τ : ℝ) : ℂ)) • Sg - (S1 - (6 : ℂ) • Dp) =
        ((2 : ℂ) • Sg - S1) + (6 : ℂ) • ((τ : ℂ) • Sg + Dp) := by
      push_cast; module
    rw [this]; exact hb.add (hc2.smul h6)
  · have : (((2 + 6 * τ : ℝ) : ℂ)) • Sg + (S1 - (6 : ℂ) • Dp) =
        ((2 : ℂ) • Sg + S1) + (6 : ℂ) • ((τ : ℂ) • Sg - Dp) := by
      push_cast; module
    rw [this]
    exact ((hSg.posSemidef.smul (by norm_num : (0 : ℂ) ≤ 2)).add hS1).add (hc1.smul h6)

end SchurLevel

section GramBlocks

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The quadratic form of a Hermitian block matrix dominates the Schur-complement form, with
equality on the minimiser (Mathlib's `schur_complement_eq₁₁`). -/
theorem schur_form_ge {X11 : Matrix m m ℂ} (hX : X11.PosDef) [Invertible X11]
    (X12 : Matrix m n ℂ) (X22 : Matrix n n ℂ) (x : m → ℂ) (y : n → ℂ) :
    star y ⬝ᵥ ((X22 - X12ᴴ * X11⁻¹ * X12) *ᵥ y) ≤
      star (x ⊕ᵥ y) ⬝ᵥ ((fromBlocks X11 X12 X12ᴴ X22) *ᵥ (x ⊕ᵥ y)) := by
  have h := schur_complement_eq₁₁ X12 X22 x y hX.1
  simp only [← dotProduct_mulVec] at h
  rw [h]
  exact le_add_of_nonneg_left (hX.posSemidef.dotProduct_mulVec_nonneg _)

theorem schur_form_eq {X11 : Matrix m m ℂ} (hX : X11.IsHermitian) [Invertible X11]
    (X12 : Matrix m n ℂ) (X22 : Matrix n n ℂ) (y : n → ℂ) :
    star ((-((X11⁻¹ * X12) *ᵥ y)) ⊕ᵥ y) ⬝ᵥ ((fromBlocks X11 X12 X12ᴴ X22) *ᵥ
        ((-((X11⁻¹ * X12) *ᵥ y)) ⊕ᵥ y)) =
      star y ⬝ᵥ ((X22 - X12ᴴ * X11⁻¹ * X12) *ᵥ y) := by
  have h := schur_complement_eq₁₁ X12 X22 (-((X11⁻¹ * X12) *ᵥ y)) y hX
  simp only [← dotProduct_mulVec] at h
  rw [h]
  simp

end GramBlocks

section GramMain

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem norm_eq_re_of_pos {z : ℂ} (hz : 0 < z) : ‖z‖ = z.re := by
  have h := Complex.lt_def.mp hz
  have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using h.2.symm)
  rw [hz', Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using h.1)]
  simp

theorem re_mul_of_pos {a b : ℂ} (ha : 0 < a) (hb : 0 < b) : (a * b).re = a.re * b.re := by
  have h1 := (Complex.lt_def.mp ha).2
  have h2 := (Complex.lt_def.mp hb).2
  rw [Complex.mul_re, ← h1, ← h2]; simp

theorem form_blockDp (Dp : Matrix n n ℂ) (x : m → ℂ) (y : n → ℂ) :
    star (x ⊕ᵥ y) ⬝ᵥ ((fromBlocks (0 : Matrix m m ℂ) (0 : Matrix m n ℂ) (0 : Matrix n m ℂ) Dp) *ᵥ
      (x ⊕ᵥ y)) = star y ⬝ᵥ (Dp *ᵥ y) := by
  simp [fromBlocks_mulVec, Function.star_sumElim]

/-- **The Gram-level form of Theorem C.3 with `b = 2`, `c = 6`** (`F(-5)` against the Cauchy
matrix `K`).  With `K = [[K₁₁, K₁₂], [K₁₂ᴴ, K₂₂]]` positive definite (weight-1 nodes first),
`F(w) = K + diag(D_-, w D_+)`:
* `F(1) ≥ 0` (`h1`), `F(1) ≤ 2K` (`h2`), `K₁₁ + D_-` positive definite (`hA`);
* `-τ K ≤ (0 ⊕ D_+) ≤ τ K` on all vectors (`h3`, `h4`), the shape given by `lemmaT_of_class`.
Then `‖det F(-5)‖ · det K₁₁ ≤ (2+6τ)^q · det(K₁₁ + D_-) · det K`, i.e.
`|det L| ≤ (2+6τ)^q det L₋₋`, `det L = det F / det K`, `det L₋₋ = det(K₁₁+D_-)/det K₁₁`. -/
theorem norm_det_gram_le {K11 : Matrix m m ℂ} {K12 : Matrix m n ℂ} {K22 Dm Dp : Matrix _ _ ℂ}
    (hK : (fromBlocks K11 K12 K12ᴴ K22).PosDef) (hA : (K11 + Dm).PosDef)
    (hDp : Dp.IsHermitian)
    (h1 : (fromBlocks (K11 + Dm) K12 K12ᴴ (K22 + Dp)).PosSemidef)
    (h2 : (fromBlocks K11 K12 K12ᴴ K22 - fromBlocks Dm 0 0 Dp).PosSemidef)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (h3 : ((τ : ℂ) • fromBlocks K11 K12 K12ᴴ K22 - fromBlocks 0 0 0 Dp).PosSemidef)
    (h4 : ((τ : ℂ) • fromBlocks K11 K12 K12ᴴ K22 + fromBlocks 0 0 0 Dp).PosSemidef) :
    ‖(fromBlocks (K11 + Dm) K12 K12ᴴ (K22 - (5 : ℂ) • Dp)).det‖ * K11.det.re ≤
      (2 + 6 * τ) ^ Fintype.card n * (K11 + Dm).det.re *
        (fromBlocks K11 K12 K12ᴴ K22).det.re := by
  classical
  have hK11 : K11.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · have := hK.1.submatrix (Sum.inl : m → m ⊕ n)
      convert this using 1
      ext i j; simp
    · have h := hK.dotProduct_mulVec_pos (x := x ⊕ᵥ (0 : n → ℂ))
        (by intro h; apply hx; funext i; simpa using congrFun h (Sum.inl i))
      simpa [fromBlocks_mulVec, Function.star_sumElim] using h
  have : Invertible K11 := hK11.isUnit.invertible
  have : Invertible (K11 + Dm) := hA.isUnit.invertible
  have hSgpos : (K22 - K12ᴴ * K11⁻¹ * K12).PosDef := by
    have hsemi := (PosDef.fromBlocks₁₁ K12 K22 hK11).mp hK.posSemidef
    refine PosDef.of_dotProduct_mulVec_pos hsemi.1 fun y hy => ?_
    rw [← schur_form_eq hK11.1 K12 K22 y]
    refine hK.dotProduct_mulVec_pos ?_
    intro hc
    apply hy
    funext j
    simpa using congrFun hc (Sum.inr j)
  have hS1 : (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12).PosSemidef :=
    (PosDef.fromBlocks₁₁ K12 (K22 + Dp) hA).mp h1
  have hτc : (0 : ℂ) ≤ (τ : ℂ) := Complex.zero_le_real.mpr hτ
  have hSgH := hSgpos.1
  -- the minimiser
  have hFsplit : fromBlocks (K11 + Dm) K12 K12ᴴ (K22 + Dp) =
      fromBlocks K11 K12 K12ᴴ K22 + fromBlocks Dm 0 0 Dp := by
    ext (i | i) (j | j) <;> simp [fromBlocks]
  have hb : ((2 : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) -
      (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12)).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · exact (hSgH.smul (by rw [IsSelfAdjoint, Complex.star_def]; simp [Complex.conj_ofNat])).sub
        hS1.1
    · have e1 := schur_form_eq hK11.1 K12 K22 y
      have e2 := schur_form_ge hA K12 (K22 + Dp) (-((K11⁻¹ * K12) *ᵥ y)) y
      have e3 := h2.dotProduct_mulVec_nonneg ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y)
      rw [hFsplit, add_mulVec, dotProduct_add] at e2
      rw [sub_mulVec, dotProduct_sub] at e3
      have e4 : star y ⬝ᵥ (((2 : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) -
          (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12)) *ᵥ y) =
          2 * (star y ⬝ᵥ ((K22 - K12ᴴ * K11⁻¹ * K12) *ᵥ y)) -
            star y ⬝ᵥ ((K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12) *ᵥ y) := by
        rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]; simp
      rw [e4, ← e1]
      set P := star ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y) ⬝ᵥ (fromBlocks K11 K12 K12ᴴ K22 *ᵥ
        ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y))
      set Q := star ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y) ⬝ᵥ (fromBlocks Dm 0 0 Dp *ᵥ
        ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y))
      set U := star y ⬝ᵥ ((K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12) *ᵥ y)
      have : 2 * P - U = (P - Q) + ((P + Q) - U) := by ring
      rw [this]
      exact add_nonneg e3 (sub_nonneg.mpr e2)
  have hc1 : ((τ : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) - Dp).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · exact (hSgH.smul (by rw [IsSelfAdjoint, Complex.star_def]; simp)).sub hDp
    · have e1 := schur_form_eq hK11.1 K12 K22 y
      have e3 := h3.dotProduct_mulVec_nonneg ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y)
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, form_blockDp, e1] at e3
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]
      exact e3
  have hc2 : ((τ : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) + Dp).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · exact (hSgH.smul (by rw [IsSelfAdjoint, Complex.star_def]; simp)).add hDp
    · have e1 := schur_form_eq hK11.1 K12 K22 y
      have e3 := h4.dotProduct_mulVec_nonneg ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y)
      rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, form_blockDp, e1] at e3
      rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul]
      exact e3
  have hmain := norm_det_schur_le hSgpos hS1 hDp hτ hb hc1 hc2
  -- determinants
  have hdF : (fromBlocks (K11 + Dm) K12 K12ᴴ (K22 - (5 : ℂ) • Dp)).det =
      (K11 + Dm).det * (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12 - (6 : ℂ) • Dp).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
    congr 2
    module
  have hdK : (fromBlocks K11 K12 K12ᴴ K22).det =
      K11.det * (K22 - K12ᴴ * K11⁻¹ * K12).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hA0 := hA.det_pos
  have hK0 := hK11.det_pos
  have hS0 := hSgpos.det_pos
  rw [hdF, hdK, norm_mul, norm_eq_re_of_pos hA0, re_mul_of_pos hK0 hS0]
  have ha := (Complex.lt_def.mp hA0).1
  have hk := (Complex.lt_def.mp hK0).1
  simp only [Complex.zero_re] at ha hk
  calc (K11 + Dm).det.re * ‖(K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12 - (6 : ℂ) • Dp).det‖ *
        K11.det.re
      ≤ (K11 + Dm).det.re * ((2 + 6 * τ) ^ Fintype.card n *
          (K22 - K12ᴴ * K11⁻¹ * K12).det.re) * K11.det.re := by
        gcongr
    _ = _ := by ring

end GramMain

section Consumer

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric OAI.InternalCatalan Filter Set

/-- The sheet product **without** the factor `(∏ (1 + s_i))^m` (PROOF-RHO §2.5, §5):
`|det markedLaurentMatrix| · ∏ paramRowNodeWeight(y_j) · paramPinPrincipal / ∏ |rowCommonFactor(y_j)|`. -/
def markedSheetCore (P : Parameters) (N : ℕ) {p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  let marked : Fin (P.n N) → Bool := fun i =>
    Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)
  |(markedLaurentMatrix (P.g N) z marked).det| *
    (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s /
      ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

/-- `markedSheetProduct` is the removed factor times the core. -/
theorem markedSheetProduct_eq_factor_mul_core (P : Parameters) (N : ℕ) {p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    markedSheetProduct P N hpm x y s = (∏ i, (1 + s i)) ^ m * markedSheetCore P N hpm x y s := by
  unfold markedSheetProduct markedSheetCore
  simp only
  ring

/-- **Statement of the signed second-case sheet bound, factor-free form (the A9 statement).**
Same hypotheses as `SignedSecondSheet` (PHASE0 §2.3) but for `markedSheetCore`, with the cost per
marked row and unit `N` a parameter `c2` (PROOF-RHO: `58 c₂''`) instead of a hard-coded constant.
The prefactor `5^m (1 + 10 e^12 n)^n` is `exp(o(N²))` for `m ≤ n`. -/
def SignedSecondSheetCore (P : Parameters) (G : ℝ → Prop) (target0 c2 alpha1 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (m : ℝ) ≤ alpha1 * (P.n N : ℝ) →
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Set.Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Set.Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1 →
      markedSheetCore P N hpm x y s ≤
        5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m)

end Consumer

section CauchyInverse

open Polynomial in
/-- Lagrange interpolation for an arbitrary node type (generalises `lagrange_sum` to polynomials
`f` of degree `< card ι`): `∑_c f(x_c) / ((1 - x_a x_c) ∏_{c'≠c}(x_c - x_c')) =
x_a^{k-1} f(1/x_a) / w(x_a)`. -/
theorem lagrange_poly {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0)
    (hw : ∀ a c, 1 - x c * x a ≠ 0) (f : ℝ[X]) (hf : f.degree < Fintype.card ι) (a : ι) :
    ∑ c, f.eval (x c) / ((1 - x a * x c) * ∏ c' ∈ Finset.univ.erase c, (x c - x c')) =
      x a ^ (Fintype.card ι - 1) * f.eval (x a)⁻¹ / ∏ c, (1 - x c * x a) := by
  have hI := Lagrange.eq_interpolate (s := Finset.univ) (v := x) (f := f) hinj.injOn (by
    rw [Finset.card_univ]; exact hf)
  have hy := congrArg (Polynomial.eval (x a)⁻¹) hI
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
    Lagrange.basis, eval_prod, Lagrange.basisDivisor, Finset.prod_mul_distrib, eval_sub, eval_X,
    Finset.prod_inv_distrib] at hy
  set y := (x a)⁻¹ with hydef
  have hxa := hx0 a
  have hxy : x a * y = 1 := by rw [hydef]; field_simp
  have hwne : ∏ c, (1 - x c * x a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hw a c
  have hE : ∀ c, ∏ c' ∈ Finset.univ.erase c, (y - x c') =
      y ^ (Fintype.card ι - 1) * ((∏ c, (1 - x c * x a)) / (1 - x c * x a)) := by
    intro c
    have step : ∀ c', y - x c' = y * (1 - x a * x c') := by
      intro c'
      have : y * (x a * x c') = x c' := by rw [← mul_assoc, mul_comm y, hxy, one_mul]
      linarith [this]
    rw [Finset.prod_congr rfl (fun c' _ => step c'), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]
    congr 1
    rw [eq_div_iff (hw a c)]
    rw [← Finset.prod_erase_mul Finset.univ (fun c' => 1 - x c' * x a) (Finset.mem_univ c)]
    congr 1
    exact Finset.prod_congr rfl (fun c' _ => by rw [mul_comm])
  have hy' : f.eval y = y ^ (Fintype.card ι - 1) * (∏ c, (1 - x c * x a)) *
      ∑ c, f.eval (x c) / ((1 - x a * x c) * ∏ c' ∈ Finset.univ.erase c, (x c - x c')) := by
    rw [hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hE c]
    have h1 := hw a c
    have h2 : 1 - x a * x c ≠ 0 := by rw [mul_comm]; exact hw a c
    have h3 : ∏ c' ∈ Finset.univ.erase c, (x c - x c') ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun c' hc' =>
        sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hc').1 (hinj h).symm)
    rw [mul_comm (x a) (x c)] at h2 ⊢
    field_simp
    congr 1
    exact Finset.prod_congr rfl fun c' _ => by ring
  set S := ∑ c, f.eval (x c) / ((1 - x a * x c) * ∏ c' ∈ Finset.univ.erase c, (x c - x c'))
    with hS
  rw [eq_div_iff hwne]
  calc S * (∏ c, (1 - x c * x a))
      = (x a ^ (Fintype.card ι - 1) * y ^ (Fintype.card ι - 1)) *
          (S * (∏ c, (1 - x c * x a))) := by
        rw [← mul_pow, hxy, one_pow, one_mul]
    _ = x a ^ (Fintype.card ι - 1) * (y ^ (Fintype.card ι - 1) * (∏ c, (1 - x c * x a)) * S) := by
        ring
    _ = x a ^ (Fintype.card ι - 1) * f.eval y := by rw [← hy']

/-- `∏_{c' ≠ c}(x_c - x_c')` is nonzero for injective `x`. -/
theorem nodal_ne_zero' {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → ℝ}
    (hinj : Function.Injective x) (c : ι) : ∏ c' ∈ Finset.univ.erase c, (x c - x c') ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun c' hc' =>
    sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hc').1 (hinj h).symm)

/-- **Cauchy-inverse identity, entrywise** (real form):
`∑_c K_{ac} B'(x_c)⁻¹ K_{cb} = δ_{ab} B'(x_a)` with `K = [1/(1 - x_a x_b)]`,
`B'(x_a) = ∏_{c≠a}(x_a - x_c) / ∏_c (1 - x_c x_a)`. -/
theorem cauchy_inverse_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0) (hw : ∀ a c, 1 - x c * x a ≠ 0)
    (a b : ι) :
    ∑ c, (1 / (1 - x a * x c)) *
        ((∏ c', (1 - x c' * x c)) / ∏ c' ∈ Finset.univ.erase c, (x c - x c')) *
        (1 / (1 - x c * x b)) =
      if a = b then (∏ c' ∈ Finset.univ.erase a, (x a - x c')) / ∏ c', (1 - x c' * x a)
      else 0 := by
  classical
  set f : Polynomial ℝ := ∏ d ∈ Finset.univ.erase b,
    (1 - Polynomial.C (x d) * Polynomial.X) with hf
  have hnat : f.natDegree ≤ Fintype.card ι - 1 := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ d ∈ Finset.univ.erase b, (1 - Polynomial.C (x d) * Polynomial.X : Polynomial ℝ).natDegree
        ≤ ∑ _d ∈ Finset.univ.erase b, 1 :=
          Finset.sum_le_sum fun d _ => by
            refine (Polynomial.natDegree_sub_le _ _).trans ?_
            simp only [Polynomial.natDegree_one, zero_le, max_le_iff]
            exact ⟨trivial, (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_le (R := ℝ))⟩
      _ = Fintype.card ι - 1 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]
          simp
  have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨b⟩
  have hdeg : f.degree < Fintype.card ι := by
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast lt_of_le_of_lt hnat (Nat.sub_lt hcard one_pos)
  have hev : ∀ y, f.eval y = ∏ d ∈ Finset.univ.erase b, (1 - x d * y) := by
    intro y; simp [hf, Polynomial.eval_prod]
  have hterm : ∀ c, (1 / (1 - x a * x c)) *
        ((∏ c', (1 - x c' * x c)) / ∏ c' ∈ Finset.univ.erase c, (x c - x c')) *
        (1 / (1 - x c * x b)) =
      f.eval (x c) / ((1 - x a * x c) * ∏ c' ∈ Finset.univ.erase c, (x c - x c')) := by
    intro c
    rw [hev]
    have h := Finset.prod_erase_mul Finset.univ (fun d => 1 - x d * x c) (Finset.mem_univ b)
    have hne : 1 - x c * x b ≠ 0 := hw b c
    have hne0 : 1 - x c * x b ≠ 0 := hw b c
    have hne2 : 1 - x a * x c ≠ 0 := by rw [mul_comm]; exact hw a c
    have hn3 := nodal_ne_zero' hinj c
    rw [← h]
    have hcomm : x c * x b = x b * x c := mul_comm _ _
    rw [hcomm] at hne ⊢
    field_simp
  rw [Finset.sum_congr rfl (fun c _ => hterm c), lagrange_poly x hinj hx0 hw f hdeg a]
  have hxa := hx0 a
  have hprod : x a ^ (Fintype.card ι - 1) * f.eval (x a)⁻¹ =
      ∏ d ∈ Finset.univ.erase b, (x a - x d) := by
    rw [hev]
    have hc : x a ^ (Fintype.card ι - 1) = ∏ _d ∈ Finset.univ.erase b, x a := by
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]
    rw [hc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun d _ => ?_
    field_simp
  rw [hprod]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [if_neg hab]
    have : ∏ d ∈ Finset.univ.erase b, (x a - x d) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩) (sub_self _)
    rw [this]; simp

end CauchyInverse

section PickMatrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Cauchy/Szegő matrix `K = [1/(1 - x_a x_b)]` over `ℂ`. -/
def kC (x : ι → ℝ) : Matrix ι ι ℂ := Matrix.of fun a b => ((1 / (1 - x a * x b) : ℝ) : ℂ)

/-- A real diagonal matrix over `ℂ`. -/
def diagC (d : ι → ℝ) : Matrix ι ι ℂ := Matrix.diagonal fun a => (d a : ℂ)

/-- `B'(x_a)` for the node set `x`. -/
def bdr (x : ι → ℝ) (a : ι) : ℝ :=
  (∏ c ∈ Finset.univ.erase a, (x a - x c)) / ∏ c, (1 - x c * x a)

theorem diagC_mul (d d' : ι → ℝ) : diagC d * diagC d' = diagC (fun a => d a * d' a) := by
  unfold diagC
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  push_cast
  rfl

theorem diagC_conjTranspose (d : ι → ℝ) : (diagC d)ᴴ = diagC d := by
  unfold diagC
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp

theorem kC_conjTranspose (x : ι → ℝ) : (kC x)ᴴ = kC x := by
  ext a b
  simp only [kC, Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def,
    Complex.conj_ofReal]
  rw [mul_comm (x b) (x a)]

theorem one_sub_mul_ne {x : ι → ℝ} (hx : ∀ a, |x a| < 1) (a c : ι) : 1 - x c * x a ≠ 0 := by
  have h1 := hx a
  have h2 := hx c
  rw [abs_lt] at h1 h2
  intro hz
  nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem bdr_ne_zero {x : ι → ℝ} (hinj : Function.Injective x) (hx : ∀ a, |x a| < 1) (a : ι) :
    bdr x a ≠ 0 := by
  unfold bdr
  exact div_ne_zero (nodal_ne_zero' hinj a)
    (Finset.prod_ne_zero_iff.mpr fun c _ => one_sub_mul_ne hx a c)

/-- **Cauchy-inverse identity** `K · diag(1/B') · K = diag(B')`. -/
theorem kC_mul_inv_mul {x : ι → ℝ} (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0)
    (hx : ∀ a, |x a| < 1) :
    kC x * diagC (fun a => (bdr x a)⁻¹) * kC x = diagC (bdr x) := by
  ext a b
  have hKD : ∀ a c, (kC x * diagC (fun a => (bdr x a)⁻¹)) a c = kC x a c * (((bdr x c)⁻¹ : ℝ) : ℂ) := by
    intro a c; unfold diagC; rw [Matrix.mul_diagonal]
  have h := cauchy_inverse_apply x hinj hx0 (one_sub_mul_ne hx) a b
  have hinv : ∀ c, (bdr x c)⁻¹ =
      (∏ c', (1 - x c' * x c)) / ∏ c' ∈ Finset.univ.erase c, (x c - x c') := by
    intro c; unfold bdr; rw [inv_div]
  have hreal : ∑ c, (1 / (1 - x a * x c)) * (bdr x c)⁻¹ * (1 / (1 - x c * x b)) =
      if a = b then bdr x a else 0 := by
    simp only [hinv]; exact h
  rw [Matrix.mul_apply]
  simp only [hKD]
  simp only [kC, diagC, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl] at hreal
    simp only [if_true]
    have := congrArg (fun r : ℝ => (r : ℂ)) hreal
    push_cast at this ⊢
    exact this
  · rw [if_neg hab] at hreal
    simp only [if_neg hab]
    have := congrArg (fun r : ℝ => (r : ℂ)) hreal
    push_cast at this ⊢
    exact this

/-- `K` is positive semidefinite (Pick/Szegő kernel). -/
theorem posSemidef_kC {x : ι → ℝ} (hx : ∀ a, |x a| < 1) : (kC x).PosSemidef := by
  have h := CatalanMeasure.GenD.Signed.posSemidef_geomGram_tsum (fun a => (x a : ℂ))
    (fun a => by simpa using hx a)
  convert h using 1
  ext a b
  simp only [kC, Matrix.of_apply, Complex.star_def, Complex.conj_ofReal]
  push_cast
  rw [one_div]

/-- `K - X^e K X = [∑_{m<e} (x_a x_b)^m]` is positive semidefinite. -/
theorem posSemidef_kC_sub {x : ι → ℝ} (hx : ∀ a, |x a| < 1) (e : ℕ) :
    (kC x - diagC (fun a => x a ^ e) * kC x * diagC (fun a => x a ^ e)).PosSemidef := by
  have h := CatalanMeasure.GenD.Signed.posSemidef_geomGram (fun a => (x a : ℂ)) e
  convert h using 1
  ext a b
  have ht : ((x a : ℂ) * (x b : ℂ)) ≠ 1 := by
    intro h1
    have h2 : x a * x b = 1 := by exact_mod_cast h1
    have h3 : 1 - x b * x a ≠ 0 := one_sub_mul_ne hx a b
    apply h3; rw [mul_comm]; linarith
  simp only [kC, diagC, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply, Complex.star_def,
    Complex.conj_ofReal]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [geom_sum_eq ht]
  have h1 : (1 - (x a : ℂ) * x b) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have h2 : (x a : ℂ) * x b - 1 ≠ 0 := sub_ne_zero.mpr ht
  push_cast
  field_simp
  ring

/-- **Pick, from the Cauchy-inverse identity.**  For `s = ±1`, `K + s · diag(B'(x_a) x_a^e)` is
positive semidefinite; in particular `F(1) ≥ 0` and `F(1) ≤ 2K`. -/
theorem posSemidef_kC_add_sign {x : ι → ℝ} (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0)
    (hx : ∀ a, |x a| < 1) (e : ℕ) {s : ℝ} (hs : s * s = 1) :
    (kC x + (s : ℂ) • diagC (fun a => bdr x a * x a ^ e)).PosSemidef := by
  set K := kC x with hK
  set H := diagC (bdr x) with hH
  set Hi := diagC (fun a => (bdr x a)⁻¹) with hHi
  set X := diagC (fun a => x a ^ e) with hX
  set T := Hi * K * X with hT
  have rK : K * Hi * K = H := kC_mul_inv_mul hinj hx0 hx
  have rHHi : H * Hi = 1 := by
    rw [hH, hHi, diagC_mul]
    unfold diagC
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    simp [mul_inv_cancel₀ (bdr_ne_zero hinj hx a)]
  have rHX : H * X = diagC (fun a => bdr x a * x a ^ e) := by
    rw [hH, hX, diagC_mul]
  have rXH : X * H = diagC (fun a => bdr x a * x a ^ e) := by
    rw [hH, hX, diagC_mul]
    unfold diagC
    congr 1
    funext a
    push_cast
    ring
  have hKh : Kᴴ = K := kC_conjTranspose x
  have hHih : Hiᴴ = Hi := diagC_conjTranspose _
  have hXh : Xᴴ = X := diagC_conjTranspose _
  have hTh : Tᴴ = X * K * Hi := by
    rw [hT, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hKh, hHih, hXh]
    simp only [Matrix.mul_assoc]
  have e1 : K * T = diagC (fun a => bdr x a * x a ^ e) := by
    calc K * T = (K * Hi * K) * X := by simp only [hT, Matrix.mul_assoc]
      _ = _ := by rw [rK, rHX]
  have e2 : Tᴴ * K = diagC (fun a => bdr x a * x a ^ e) := by
    calc Tᴴ * K = X * (K * Hi * K) := by rw [hTh]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [rK, rXH]
  have e3 : Tᴴ * K * T = X * K * X := by
    calc Tᴴ * K * T = (X * H) * (Hi * K * X) := by rw [e2, ← rXH, hT]
      _ = X * (H * Hi) * K * X := by simp only [Matrix.mul_assoc]
      _ = X * K * X := by rw [rHHi]; simp only [Matrix.mul_one]
  set A : Matrix ι ι ℂ := 1 + (s : ℂ) • T with hA
  have hAh : Aᴴ = 1 + (s : ℂ) • Tᴴ := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul]
    simp [Complex.star_def, Complex.conj_ofReal]
  have hQ : (Aᴴ * K * A).PosSemidef := (posSemidef_kC hx).conjTranspose_mul_mul_same A
  have hexp : Aᴴ * K * A = K + (s : ℂ) • (K * T) + (s : ℂ) • (Tᴴ * K) +
      ((s : ℂ) * (s : ℂ)) • (Tᴴ * K * T) := by
    rw [hAh, hA]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, smul_add]
    abel
  have hss : ((s : ℂ) * (s : ℂ)) = 1 := by exact_mod_cast hs
  have hfin : K + (s : ℂ) • diagC (fun a => bdr x a * x a ^ e) =
      (1 / 2 : ℂ) • (Aᴴ * K * A + (K - X * K * X)) := by
    rw [hexp, e3, e1, e2, hss]
    module
  rw [hfin]
  have h2 : (0 : ℂ) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by norm_num)
  exact (hQ.add (posSemidef_kC_sub hx e)).smul h2

end PickMatrices

section Transfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form of a real symmetric matrix on a complex vector is the sum of the forms on
the real and imaginary parts. -/
theorem form_map_ofReal (Mr : Matrix ι ι ℝ) (hs : ∀ a b, Mr a b = Mr b a) (v : ι → ℂ) :
    star v ⬝ᵥ ((Mr.map (fun r : ℝ => (r : ℂ))) *ᵥ v) =
      (((∑ a, ∑ b, (v a).re * Mr a b * (v b).re) +
        ∑ a, ∑ b, (v a).im * Mr a b * (v b).im : ℝ) : ℂ) := by
  have hterm : ∀ a b, star (v a) * ((Mr a b : ℝ) : ℂ) * v b =
      (((v a).re * Mr a b * (v b).re + (v a).im * Mr a b * (v b).im : ℝ) : ℂ) +
        Complex.I * (((Mr a b * ((v a).re * (v b).im - (v a).im * (v b).re) : ℝ)) : ℂ) := by
    intro a b
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  have hzero : ∑ a, ∑ b, Mr a b * ((v a).re * (v b).im - (v a).im * (v b).re) = 0 := by
    have h1 : ∑ a, ∑ b, Mr a b * ((v a).re * (v b).im - (v a).im * (v b).re) =
        (∑ a, ∑ b, Mr a b * ((v a).re * (v b).im)) -
          ∑ a, ∑ b, Mr a b * ((v a).im * (v b).re) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have h2 : (∑ a, ∑ b, Mr a b * ((v a).im * (v b).re)) =
        ∑ a, ∑ b, Mr a b * ((v a).re * (v b).im) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hs b a]; ring
    rw [h1, h2]; ring
  have e1 : star v ⬝ᵥ ((Mr.map (fun r : ℝ => (r : ℂ))) *ᵥ v) =
      ∑ a, ∑ b, star (v a) * ((Mr a b : ℝ) : ℂ) * v b := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum,
      mul_assoc]
  have hz' : (((∑ a, ∑ b, Mr a b * ((v a).re * (v b).im - (v a).im * (v b).re) : ℝ)) : ℂ) = 0 := by
    rw [hzero]; simp
  rw [e1]
  simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  push_cast at hz' ⊢
  rw [hz']
  simp only [Finset.sum_add_distrib, mul_zero, add_zero]

/-- A real symmetric matrix with nonnegative real quadratic form is positive semidefinite over
`ℂ`. -/
theorem posSemidef_map_ofReal (Mr : Matrix ι ι ℝ) (hs : ∀ a b, Mr a b = Mr b a)
    (h : ∀ u : ι → ℝ, 0 ≤ ∑ a, ∑ b, u a * Mr a b * u b) :
    (Mr.map (fun r : ℝ => (r : ℂ))).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · show (Mr.map (fun r : ℝ => (r : ℂ)))ᴴ = Mr.map (fun r : ℝ => (r : ℂ))
    ext a b
    simp [Matrix.conjTranspose_apply, hs a b]
  · rw [form_map_ofReal Mr hs v]
    have := add_nonneg (h fun a => (v a).re) (h fun a => (v a).im)
    exact Complex.zero_le_real.mpr this

end Transfer

section WeightedLemma51

open CatalanMeasure.GenD.Signed

/-- `D_ω = diag(ω_b B_-'(x_b) x_b^e)` (weights `ω_b` on all nodes). -/
noncomputable def dW {k : ℕ} (ω : Fin k → ℝ) (e : ℕ) (x : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal fun b => ω b * negBlaschkeDeriv x b * x b ^ e

/-- The `k × k` matrix `[x_b^j + ω_b x_b^{m-j}]`. -/
noncomputable def dMatW {k : ℕ} (ω : Fin k → ℝ) (m : ℕ) (x : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun b j => x b ^ (j : ℕ) + ω b * x b ^ (m - (j : ℕ))

/-- **Lemma 5.1 with signed weights on all nodes** (the Laurent-to-Gram determinant identity):
`det (K + D_ω) / det K = det [x_b^j + ω_b x_b^{m-j}] / V(x)`, `m = e + k - 1`.  Same proof as
`lemma51` (which is the case `ω_b = B_G(x_b)`). -/
theorem lemma51_weighted {k : ℕ} (ω : Fin k → ℝ) (e : ℕ) (x : Fin k → ℝ)
    (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0) (hx1 : ∀ b, |x b| < 1) :
    (kMat x + dW ω e x).det / (kMat x).det =
      (dMatW ω (e + k - 1) x).det / (Matrix.vandermonde x).det := by
  have hw : ∀ a c, 1 - x c * x a ≠ 0 := by
    intro a c hz
    have h1 := hx1 a
    have h2 := hx1 c
    rw [abs_lt] at h1 h2
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hw' : ∀ a, wFun x (x a) ≠ 0 := fun a =>
    Finset.prod_ne_zero_iff.mpr fun c _ => hw a c
  have hn : ∀ c, nodalProd x c ≠ 0 := nodalProd_ne_zero hinj
  set V := Matrix.vandermonde x with hV
  set rv : Equiv.Perm (Fin k) := Fin.revPerm with hrv
  have hrev : ∀ j : Fin k, ((rv j : Fin k) : ℕ) = k - 1 - (j : ℕ) := by
    intro j; simp only [hrv, Fin.revPerm_apply, Fin.val_rev]; omega
  set Q : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun c j => x c ^ (j : ℕ) / nodalProd x c with hQ
  have hQdiag : Q = Matrix.diagonal (fun c => (nodalProd x c)⁻¹) * V := by
    ext c j
    simp [hQ, hV, Matrix.diagonal_mul, Matrix.vandermonde_apply, div_eq_inv_mul]
  have hKQ : kMat x * Q = Matrix.diagonal (fun a => (wFun x (x a))⁻¹) * V.submatrix id rv := by
    ext a j
    rw [Matrix.diagonal_mul]
    simp only [Matrix.mul_apply, kMat, hQ, Matrix.of_apply, Matrix.submatrix_apply, id, hV,
      Matrix.vandermonde_apply, hrev]
    have := lagrange_sum x hinj hx0 hw a j j.2
    rw [← div_eq_inv_mul, ← this]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h2 : 1 - x a * x c ≠ 0 := by rw [mul_comm]; exact hw a c
    have h3 := hn c
    field_simp
  have hDQ : dW ω e x * Q = Matrix.diagonal (fun a => (wFun x (x a))⁻¹) *
      (Matrix.diagonal (fun a => ω a * x a ^ e) * V) := by
    ext a j
    simp only [dW, Matrix.diagonal_mul, hQ, Matrix.of_apply, hV, Matrix.vandermonde_apply,
      negBlaschkeDeriv]
    have h3 := hn a
    have h4 := hw' a
    field_simp
  have hdM : (dMatW ω (e + k - 1) x).submatrix id rv =
      V.submatrix id rv + Matrix.diagonal (fun a => ω a * x a ^ e) * V := by
    ext a j
    simp only [dMatW, Matrix.of_apply, Matrix.add_apply, hV, Matrix.vandermonde_apply,
      Matrix.diagonal_mul, Matrix.submatrix_apply, id, hrev]
    have : e + k - 1 - (k - 1 - (j : ℕ)) = e + (j : ℕ) := by have := j.2; omega
    rw [this, pow_add]
    ring
  have hKDQ : (kMat x + dW ω e x) * Q =
      Matrix.diagonal (fun a => (wFun x (x a))⁻¹) * (dMatW ω (e + k - 1) x).submatrix id rv := by
    rw [add_mul, hKQ, hDQ, hdM, mul_add]
  set sg : ℝ := (((Equiv.Perm.sign rv : ℤˣ) : ℤ) : ℝ) with hsg
  have hsg0 : sg ≠ 0 := by
    rw [hsg, hrv, sign_revPerm]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (by norm_num)
  have hX : (∏ a, (wFun x (x a))⁻¹) * sg ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a _ => inv_ne_zero (hw' a)) hsg0
  have hVdet : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hQdet : Q.det ≠ 0 := by
    rw [hQdiag, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun c _ => inv_ne_zero (hn c)) hVdet
  have A1 : (kMat x + dW ω e x).det * Q.det =
      ((∏ a, (wFun x (x a))⁻¹) * sg) * (dMatW ω (e + k - 1) x).det := by
    rw [← Matrix.det_mul, hKDQ, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute']
    ring
  have A2 : (kMat x).det * Q.det = ((∏ a, (wFun x (x a))⁻¹) * sg) * V.det := by
    rw [← Matrix.det_mul, hKQ, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute']
    ring
  have hK0 : (kMat x).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at A2
    exact mul_ne_zero hX hVdet A2.symm
  rw [div_eq_div_iff hK0 hVdet]
  apply mul_right_cancel₀ (mul_ne_zero hQdet hX)
  linear_combination (V.det * ((∏ a, (wFun x (x a))⁻¹) * sg)) * A1 -
    ((dMatW ω (e + k - 1) x).det * ((∏ a, (wFun x (x a))⁻¹) * sg)) * A2


end WeightedLemma51

section LaurentGram

open CatalanMeasure.Parametric CatalanMeasure.GenD.Signed

/-- Weight `ω(x) = 1` on negative and `-5` on positive free nodes. -/
def omegaOf (x : ℝ) : ℝ := if x < 0 then 1 else -5

/-- Prefactor `1/2` on negative and `-1/4` on positive free nodes. -/
def lamOf (x : ℝ) : ℝ := if x < 0 then 1 / 2 else -(1 / 4)

theorem abs_lamOf_le (x : ℝ) : |lamOf x| ≤ 1 / 2 := by
  unfold lamOf
  split_ifs <;> norm_num [abs_of_pos, abs_of_neg]

theorem actualLaurentEntry_eq {n g : ℕ} (hg : 2 * g + 1 ≤ n) {x : ℝ} (hx : x ≠ 0) (r : Fin n) :
    actualLaurentEntry g r x =
      lamOf x * x ^ ((g : ℤ) - (n - 1 : ℕ)) *
        (x ^ (r.rev : ℕ) + omegaOf x * x ^ ((n - 1 - 2 * g) + n - 1 - (r.rev : ℕ))) := by
  have h1 : x ^ ((g : ℤ) - (n - 1 : ℕ)) * x ^ (r.rev : ℕ) = x ^ ((g : ℤ) - r) :=
    far_laurent_factor r hx
  have h2 : x ^ ((g : ℤ) - (n - 1 : ℕ)) * x ^ ((n - 1 - 2 * g) + n - 1 - (r.rev : ℕ)) =
      x ^ ((r : ℤ) - g) := by
    first
      | rw [← zpow_natCast x _, ← zpow_add₀ hx]
      | rw [← zpow_add₀ hx]
    congr 1
    have := r.isLt
    simp only [Fin.val_rev]
    omega
  unfold actualLaurentEntry lamOf omegaOf
  split_ifs
  · rw [← h1, ← h2]; ring
  · rw [← h1, ← h2]; ring

theorem abs_det_laurent_eq {n g : ℕ} (hg : 2 * g + 1 ≤ n) (x : Fin n → ℝ) (hx0 : ∀ i, x i ≠ 0) :
    |(markedLaurentMatrix g x (fun _ => false)).det| =
      (∏ i, |lamOf (x i)| * |x i| ^ ((g : ℤ) - (n - 1 : ℕ))) *
        |(dMatW (fun i => omegaOf (x i)) ((n - 1 - 2 * g) + n - 1) x).det| := by
  have hmat : (markedLaurentMatrix g x (fun _ => false)) =
      Matrix.diagonal (fun i => lamOf (x i) * x i ^ ((g : ℤ) - (n - 1 : ℕ))) *
        (dMatW (fun i => omegaOf (x i)) ((n - 1 - 2 * g) + n - 1) x).submatrix id
          (Fin.revPerm : Equiv.Perm (Fin n)) := by
    ext i r
    simp only [markedLaurentMatrix, Matrix.of_apply, Bool.false_eq_true, if_false,
      Matrix.diagonal_mul, Matrix.submatrix_apply, id, dMatW, Fin.revPerm_apply]
    rw [actualLaurentEntry_eq hg (hx0 i) r]
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal, abs_mul, Finset.abs_prod]
  have hperm : |((dMatW (fun i => omegaOf (x i)) ((n - 1 - 2 * g) + n - 1) x).submatrix id
      (Fin.revPerm : Equiv.Perm (Fin n))).det| =
      |(dMatW (fun i => omegaOf (x i)) ((n - 1 - 2 * g) + n - 1) x).det| := by
    simpa using Matrix.abs_det_submatrix_equiv_equiv (Equiv.refl (Fin n)) (Fin.revPerm : Equiv.Perm (Fin n))
      (dMatW (fun i => omegaOf (x i)) ((n - 1 - 2 * g) + n - 1) x)
  rw [hperm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [abs_mul, abs_zpow]

end LaurentGram

section SignSplit

/-- Splitting the nodes by sign: `Fin n ≃ Fin k ⊕ Fin q` with negatives first. -/
theorem exists_sign_split {n : ℕ} (x : Fin n → ℝ) (hx0 : ∀ i, x i ≠ 0) :
    ∃ (k q : ℕ) (σ : Fin k ⊕ Fin q ≃ Fin n),
      (∀ b, x (σ (Sum.inl b)) < 0) ∧ ∀ p, 0 < x (σ (Sum.inr p)) := by
  classical
  let eS : {i // x i < 0} ≃ Fin (Fintype.card {i // x i < 0}) := Fintype.equivFin _
  let eT : {i // ¬ x i < 0} ≃ Fin (Fintype.card {i // ¬ x i < 0}) := Fintype.equivFin _
  refine ⟨Fintype.card {i // x i < 0}, Fintype.card {i // ¬ x i < 0},
    (Equiv.sumCongr eS.symm eT.symm).trans (Equiv.sumCompl (fun i => x i < 0)), ?_, ?_⟩
  · intro b
    simpa using (eS.symm b).2
  · intro p
    have h := (eT.symm p).2
    have : x (eT.symm p).1 ≠ 0 := hx0 _
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm this)

/-- Products over `univ.erase` transport along an equivalence. -/
theorem prod_erase_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (σ : ι ≃ κ) (f : κ → ℝ) (i : ι) :
    ∏ c ∈ Finset.univ.erase i, f (σ c) = ∏ c ∈ Finset.univ.erase (σ i), f c := by
  refine Finset.prod_equiv σ ?_ (fun _ _ => rfl)
  intro c
  simp [Finset.mem_erase, σ.injective.eq_iff]

theorem prod_erase_inl {k q : ℕ} (F : Fin k ⊕ Fin q → ℝ) (b : Fin k) :
    ∏ c ∈ Finset.univ.erase (Sum.inl b), F c =
      (∏ a ∈ Finset.univ.erase b, F (Sum.inl a)) * ∏ p, F (Sum.inr p) := by
  classical
  set F' : Fin k ⊕ Fin q → ℝ := fun c => if c = Sum.inl b then 1 else F c with hF'
  have h1 : ∏ c ∈ Finset.univ.erase (Sum.inl b), F c =
      ∏ c ∈ Finset.univ.erase (Sum.inl b), F' c := by
    refine Finset.prod_congr rfl fun c hc => ?_
    simp [hF', (Finset.mem_erase.mp hc).1]
  rw [h1, Finset.prod_erase _ (by simp [hF'] : F' (Sum.inl b) = 1), Fintype.prod_sum_type]
  congr 1
  · have hh := Finset.prod_erase Finset.univ (f := fun a : Fin k => F' (Sum.inl a)) (a := b)
      (by simp [hF'])
    rw [← hh]
    refine Finset.prod_congr rfl fun a ha => ?_
    simp [hF', (Finset.mem_erase.mp ha).1]
  all_goals (refine Finset.prod_congr rfl fun p _ => ?_; simp [hF'])

end SignSplit

section GramFull

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- `norm_det_gram_le` for a full matrix on the index type `m ⊕ n` with real diagonal data
(`d` on all nodes; `D_-` = `d ∘ inl`, `D_+ = d ∘ inr`). -/
theorem norm_det_gram_le_full (Kf : Matrix (m ⊕ n) (m ⊕ n) ℂ) (d : m ⊕ n → ℝ)
    (hK : Kf.PosDef) (hA : (Kf.submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a))).PosDef)
    (h1 : (Kf + diagC d).PosSemidef) (h2 : (Kf - diagC d).PosSemidef)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (h3 : ((τ : ℂ) • Kf - diagC (Sum.elim (fun _ => 0) (fun p => d (Sum.inr p)))).PosSemidef)
    (h4 : ((τ : ℂ) • Kf + diagC (Sum.elim (fun _ => 0) (fun p => d (Sum.inr p)))).PosSemidef) :
    ‖(Kf + diagC (Sum.elim (fun a => d (Sum.inl a)) (fun p => -5 * d (Sum.inr p)))).det‖ *
        (Kf.submatrix Sum.inl Sum.inl).det.re ≤
      (2 + 6 * τ) ^ Fintype.card n *
        (Kf.submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a))).det.re * Kf.det.re := by
  classical
  have hKe : ∀ i j, Kf (Sum.inr i) (Sum.inl j) = star (Kf (Sum.inl j) (Sum.inr i)) :=
    fun i j => (hK.1.apply (Sum.inr i) (Sum.inl j)).symm
  have hfb : Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ = Kf := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe]
  have hsub : Kf.submatrix Sum.inl Sum.inl = Kf.toBlocks₁₁ := rfl
  rw [hsub] at hA ⊢
  have e1 : Matrix.fromBlocks (Kf.toBlocks₁₁ + diagC (fun a => d (Sum.inl a))) Kf.toBlocks₁₂
      Kf.toBlocks₁₂ᴴ (Kf.toBlocks₂₂ + diagC (fun p => d (Sum.inr p))) = Kf + diagC d := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe, diagC, Matrix.diagonal_apply]
  have e2 : Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ -
      Matrix.fromBlocks (diagC (fun a => d (Sum.inl a))) 0 0 (diagC (fun p => d (Sum.inr p))) =
      Kf - diagC d := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe, diagC, Matrix.diagonal_apply]
  have e3 : (τ : ℂ) • Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ -
      Matrix.fromBlocks 0 0 0 (diagC (fun p => d (Sum.inr p))) =
      (τ : ℂ) • Kf - diagC (Sum.elim (fun _ => 0) (fun p => d (Sum.inr p))) := by
    rw [hfb]
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, diagC, Matrix.diagonal_apply]
  have e4 : (τ : ℂ) • Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ +
      Matrix.fromBlocks 0 0 0 (diagC (fun p => d (Sum.inr p))) =
      (τ : ℂ) • Kf + diagC (Sum.elim (fun _ => 0) (fun p => d (Sum.inr p))) := by
    rw [hfb]
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, diagC, Matrix.diagonal_apply]
  have e5 : Matrix.fromBlocks (Kf.toBlocks₁₁ + diagC (fun a => d (Sum.inl a))) Kf.toBlocks₁₂
      Kf.toBlocks₁₂ᴴ (Kf.toBlocks₂₂ - (5 : ℂ) • diagC (fun p => d (Sum.inr p))) =
      Kf + diagC (Sum.elim (fun a => d (Sum.inl a)) (fun p => -5 * d (Sum.inr p))) := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe, diagC, Matrix.diagonal_apply] <;> (try split_ifs) <;> (try simp) <;> (try ring)
  have key := norm_det_gram_le (K11 := Kf.toBlocks₁₁) (K12 := Kf.toBlocks₁₂)
    (K22 := Kf.toBlocks₂₂)
    (Dm := diagC (fun a => d (Sum.inl a))) (Dp := diagC (fun p => d (Sum.inr p)))
    (by rw [hfb]; exact hK) hA (diagC_conjTranspose _)
    (by rw [e1]; exact h1)
    (by rw [e2]; exact h2)
    hτ
    (by rw [e3]; exact h3)
    (by rw [e4]; exact h4)
  rw [e5, hfb] at key
  exact key

end GramFull

section DetFacts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real Cauchy matrix `[1/(1 - x_a x_b)]`. -/
def kR (x : ι → ℝ) : Matrix ι ι ℝ := Matrix.of fun a b => 1 / (1 - x a * x b)

theorem kC_eq_map (x : ι → ℝ) : kC x = (kR x).map (fun r : ℝ => (r : ℂ)) := rfl

theorem det_map_ofReal (M : Matrix ι ι ℝ) :
    (M.map (fun r : ℝ => (r : ℂ))).det = ((M.det : ℝ) : ℂ) := by
  have h := RingHom.map_det Complex.ofRealHom M
  rw [RingHom.mapMatrix_apply] at h
  exact h.symm

theorem diagC_inv_mul {x : ι → ℝ} (hinj : Function.Injective x) (hx : ∀ a, |x a| < 1) :
    diagC (bdr x) * diagC (fun a => (bdr x a)⁻¹) = 1 := by
  rw [diagC_mul]
  unfold diagC
  rw [← Matrix.diagonal_one]
  congr 1
  funext a
  simp [mul_inv_cancel₀ (bdr_ne_zero hinj hx a)]

theorem kC_posDef {x : ι → ℝ} (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0)
    (hx : ∀ a, |x a| < 1) : (kC x).PosDef := by
  refine ((posSemidef_kC hx).posDef_iff_isUnit).mpr ?_
  have h1 : kC x * (diagC (fun a => (bdr x a)⁻¹) * kC x * diagC (fun a => (bdr x a)⁻¹)) = 1 := by
    calc _ = (kC x * diagC (fun a => (bdr x a)⁻¹) * kC x) * diagC (fun a => (bdr x a)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [kC_mul_inv_mul hinj hx0 hx, diagC_inv_mul hinj hx]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h1)

theorem kR_det_pos {x : ι → ℝ} (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0)
    (hx : ∀ a, |x a| < 1) : 0 < (kR x).det := by
  have h := (kC_posDef hinj hx0 hx).det_pos
  rw [kC_eq_map, det_map_ofReal] at h
  exact Complex.zero_lt_real.mp h

theorem posSemidef_submatrix_inl {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {M : Matrix (m ⊕ n) (m ⊕ n) ℂ} (hM : M.PosSemidef) :
    (M.submatrix Sum.inl Sum.inl).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · exact hM.1.submatrix Sum.inl
  · have h := hM.dotProduct_mulVec_nonneg (v ⊕ᵥ (0 : n → ℂ))
    simpa [Matrix.fromBlocks_mulVec, Function.star_sumElim, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type] using h

end DetFacts

section MainDet

open CatalanMeasure.GenD.Signed CatalanMeasure.Parametric

/-- The Blaschke derivative of the full node set splits over negatives and positives. -/
theorem bdr_inl {k q : ℕ} (z : Fin k ⊕ Fin q → ℝ) (b : Fin k)
    (hz0 : ∀ i, z i ≠ 0) (hzb : ∀ p, 1 - z (Sum.inr p) * z (Sum.inl b) ≠ 0)
    (hz1 : ∀ a, 1 - z (Sum.inl a) * z (Sum.inl b) ≠ 0) :
    bdr z (Sum.inl b) = blaschkeG (hOfRoots (fun p => z (Sum.inr p))) q (z (Sum.inl b)) *
      negBlaschkeDeriv (fun a => z (Sum.inl a)) b := by
  unfold bdr
  have hpe := prod_erase_inl (fun c => z (Sum.inl b) - z c) b
  try simp only at hpe
  rw [hpe, Fintype.prod_sum_type, blaschkeG_prod _ _ (hz0 _)]
  unfold negBlaschkeDeriv nodalProd wFun
  simp only
  rw [Finset.prod_div_distrib]
  have h1 : ∏ a, (1 - z (Sum.inl a) * z (Sum.inl b)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => hz1 a
  have h2 : ∏ p, (1 - z (Sum.inr p) * z (Sum.inl b)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => hzb p
  have h3 : ∏ p, (1 - (fun p => z (Sum.inr p)) p * z (Sum.inl b)) =
      ∏ p, (1 - z (Sum.inr p) * z (Sum.inl b)) := rfl
  simp only [h3]
  field_simp

end MainDet

section MainDetPre

open CatalanMeasure.GenD.Signed CatalanMeasure.Parametric

/-- The Loewner inequality `±D ≤ τ K` (a real quadratic-form statement) as a positive
semidefiniteness statement over `ℂ`. -/
theorem posSemidef_tau_form {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι → ℝ) (dpE : ι → ℝ)
    (τ s : ℝ) (hs : s = 1 ∨ s = -1)
    (h : ∀ u : ι → ℝ, |∑ a, dpE a * u a ^ 2| ≤
      τ * ∑ a, ∑ b, u a * u b / (1 - z a * z b)) :
    ((τ : ℂ) • kC z + (s : ℂ) • diagC dpE).PosSemidef := by
  have hmat : ((τ : ℂ) • kC z + (s : ℂ) • diagC dpE) =
      ((τ • kR z + s • Matrix.diagonal dpE : Matrix ι ι ℝ)).map (fun r : ℝ => (r : ℂ)) := by
    ext a b
    simp only [kC, kR, diagC, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      Matrix.map_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hmat]
  refine posSemidef_map_ofReal _ (fun a b => ?_) (fun u => ?_)
  · simp only [Matrix.add_apply, Matrix.smul_apply, kR, Matrix.of_apply, Matrix.diagonal_apply,
      smul_eq_mul]
    rw [mul_comm (z b) (z a)]
    by_cases hab : a = b
    · subst hab; rfl
    · rw [if_neg hab, if_neg (Ne.symm hab)]
  · have e1 : ∀ a b, u a * (τ • kR z + s • Matrix.diagonal dpE) a b * u b =
        τ * (u a * u b / (1 - z a * z b)) + s * (if a = b then dpE a * u a ^ 2 else 0) := by
      intro a b
      simp only [Matrix.add_apply, Matrix.smul_apply, kR, Matrix.of_apply, Matrix.diagonal_apply,
        smul_eq_mul]
      split_ifs with hab
      · subst hab; ring
      · ring
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hh := h u
    rcases hs with rfl | rfl <;> rw [abs_le] at hh <;> nlinarith [hh.1, hh.2]


/-- **Pick: `F(1) ≥ 0`.**  `K + diag(B'(x_a) x_a^e)` is positive semidefinite. -/
theorem pick_F_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → ℝ}
    (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0) (hx : ∀ a, |x a| < 1) (e : ℕ) :
    (kC x + diagC (fun a => bdr x a * x a ^ e)).PosSemidef := by
  simpa using posSemidef_kC_add_sign hinj hx0 hx e (s := 1) (by norm_num)

/-- **Pick: `F(1) ≤ 2K`.**  `K - diag(B'(x_a) x_a^e)` is positive semidefinite. -/
theorem pick_F_le_two_K {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → ℝ}
    (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0) (hx : ∀ a, |x a| < 1) (e : ℕ) :
    (kC x - diagC (fun a => bdr x a * x a ^ e)).PosSemidef := by
  simpa [sub_eq_add_neg] using posSemidef_kC_add_sign hinj hx0 hx e (s := -1) (by norm_num)

/-- **Real-to-complex transfer of Lemma T:** the Loewner inequalities `±(0 ⊕ D₊) ≤ (3/2) K`
over `ℂ` (the hypotheses `h3`, `h4` of `norm_det_gram_le`) from the real form. -/
theorem lemmaT_loewner_complex {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι → ℝ) (dpE : ι → ℝ)
    (h : ∀ u : ι → ℝ, |∑ a, dpE a * u a ^ 2| ≤
      (3 / 2) * ∑ a, ∑ b, u a * u b / (1 - z a * z b)) :
    ((((3 / 2 : ℝ) : ℂ) • kC z - diagC dpE).PosSemidef) ∧
      ((((3 / 2 : ℝ) : ℂ) • kC z + diagC dpE).PosSemidef) := by
  refine ⟨?_, ?_⟩
  · simpa [sub_eq_add_neg] using posSemidef_tau_form z dpE (3 / 2) (-1) (Or.inr rfl) h
  · simpa using posSemidef_tau_form z dpE (3 / 2) 1 (Or.inl rfl) h

end MainDetPre

section MainDet2

open CatalanMeasure.GenD.Signed CatalanMeasure.Parametric

end MainDet2

section SheetBridge

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan Filter Set

/-- The empty family of reals. -/
def e0 : Fin 0 → ℝ := fun i => i.elim0

theorem fin_append_nil (n : ℕ) (x : Fin n → ℝ) (y : Fin 0 → ℝ) :
    (Fin.append x y : Fin (n + 0) → ℝ) = x := by
  funext i
  exact Fin.append_left x y i

/-- For `m = 0` the sheet core is `|det Laurent| · pin`. -/
theorem markedSheetCore_zero_eq {P : Parameters} {N : ℕ} (hpm : P.n N + 0 = P.n N)
    (x s : Fin (P.n N) → ℝ) :
    markedSheetCore P N hpm x e0 s =
      |(markedLaurentMatrix (P.g N) x (fun _ => false)).det| * paramPinPrincipal P N x s := by
  have hz : (fun i : Fin (P.n N) => Fin.append x e0 (Fin.cast hpm.symm i)) = x := by
    funext i
    have : Fin.cast hpm.symm i = Fin.castAdd 0 i := Fin.ext rfl
    rw [this, Fin.append_left]
  have hm : (fun i : Fin (P.n N) =>
      Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i) : Fin (P.n N) → Bool) =
      fun _ => false := by
    funext i
    have : Fin.cast hpm.symm i = Fin.castAdd 0 i := Fin.ext rfl
    rw [this, Fin.addCases_left]
  unfold markedSheetCore
  simp only [hz, hm]
  simp

/-- For `a = b = 0` the grouped product is `∏|x|^{g-(n-1)} · |V(x)| · pin`. -/
theorem groupedProduct_zero_eq (P : Parameters) (N : ℕ) (x s : Fin (P.n N) → ℝ) :
    groupedProduct P N x e0 e0 s =
      (∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) * |(Matrix.vandermonde x).det| *
        paramPinPrincipal P N x s := by
  have hap : (Fin.append x e0 : Fin (P.n N + 0) → ℝ) = x := fin_append_nil _ x e0
  unfold groupedProduct groupedPairProduct crossCauchyProduct
  rw [hap, Matrix.det_vandermonde]
  simp

/-- The grouped value at `a = b = 0` (the free-point population). -/
def signedValue (P : Parameters) (N : ℕ) (x s : Fin (P.n N) → ℝ) : ℝ :=
  groupedValueWithFields (P.n N : ℝ) (groupedConstant P N (P.n N) 0 0)
    (populationPhysicalFreeField P N) (groupedMarkedField P N) (groupedNearField P N)
    (populationPhysicalColumnField P N (0 + 0)) x e0 e0 s

theorem log_groupedProduct_zero {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (x s : Fin (P.n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (groupedProduct P N x e0 e0 s) = (P.n N : ℝ) ^ 2 * signedValue P N x s := by
  have hap : (Fin.append x e0 : Fin (P.n N + 0) → ℝ) = x := fin_append_nil _ x e0
  exact log_groupedProduct hP hN x e0 e0 s hx (fun i => i.elim0) (fun i => i.elim0) hs hx0
    (fun i => i.elim0) hxi (by rw [hap]; exact hxi) (fun i => i.elim0) hsi

theorem groupedProduct_zero_pos {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (x s : Fin (P.n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    0 < groupedProduct P N x e0 e0 s := by
  rw [groupedProduct_zero_eq]
  have h1 : 0 < ∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) :=
    Finset.prod_pos fun i _ => zpow_pos (abs_pos.mpr (hx0 i)) _
  have h2 : 0 < |(Matrix.vandermonde x).det| :=
    abs_pos.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hxi)
  exact mul_pos (mul_pos h1 h2) (paramPinPrincipal_pos hP hN x s hx hs hx0 hxi hsi)

/-- `11^q ≤ (1 + 10 e^12 n)^n` for `q ≤ n`, `n ≥ 1`. -/
theorem eleven_pow_le {n q : ℕ} (hq : q ≤ n) (hn : 1 ≤ n) :
    (11 : ℝ) ^ q ≤ (1 + 10 * Real.exp 12 * (n : ℝ)) ^ n := by
  have h1 : (11 : ℝ) ^ q ≤ 11 ^ n := pow_le_pow_right₀ (by norm_num) hq
  have h2 : (11 : ℝ) ≤ 1 + 10 * Real.exp 12 * (n : ℝ) := by
    have he : (1 : ℝ) ≤ Real.exp 12 := Real.one_le_exp (by norm_num)
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  exact h1.trans (pow_le_pow_left₀ (by norm_num) h2 n)

end SheetBridge

section SignedSheet

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan Filter Set

end SignedSheet


end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.norm_det_le_of_loewner_gram
#print axioms CatalanMeasure.Signed.norm_det_schur_le
#print axioms CatalanMeasure.Signed.norm_det_gram_le
#print axioms CatalanMeasure.Signed.markedSheetProduct_eq_factor_mul_core
#print axioms CatalanMeasure.Signed.lagrange_poly
#print axioms CatalanMeasure.Signed.cauchy_inverse_apply
#print axioms CatalanMeasure.Signed.kC_mul_inv_mul
#print axioms CatalanMeasure.Signed.pick_F_nonneg
#print axioms CatalanMeasure.Signed.pick_F_le_two_K
#print axioms CatalanMeasure.Signed.posSemidef_map_ofReal
#print axioms CatalanMeasure.Signed.lemmaT_loewner_complex
#print axioms CatalanMeasure.Signed.exists_sign_split
#print axioms CatalanMeasure.Signed.lemma51_weighted
#print axioms CatalanMeasure.Signed.abs_det_laurent_eq
#print axioms CatalanMeasure.Signed.norm_det_gram_le_full
