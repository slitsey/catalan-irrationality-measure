module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The relative-norm lemma for a positive definite pencil (ledger ZA14)

Fauzan's pencil is `G_K(X) = G + (X - ξ) M` with `G` positive definite and `M` symmetric.
With `B = G^{-1/2} M G^{-1/2}`, `det(G + δ M) = det G · det(I + δ B)`.  The hypothesis
`‖B‖ ≤ β` is stated without square roots as the quadratic-form inequality
`|vᵀ M v| ≤ β · vᵀ G v` for all `v` (this is exactly `-β G ≤ M ≤ β G`).

`det_pencil_bounds`: if `|δ| β h ≤ 1/2` (h the size), then `0 < det(G + δ M) ≤ 2 det G`.
-/

open Matrix
open scoped MatrixOrder

namespace Apery

/-- `exp (1/2) ≤ 2`. -/
lemma exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

/-- **ZA14.**  Relative-norm bound for a positive definite pencil. -/
theorem det_pencil_bounds {h : ℕ} (G M : Matrix (Fin h) (Fin h) ℝ) (hG : G.PosDef)
    (hMs : Mᵀ = M) (β δ : ℝ)
    (hβ : ∀ v : Fin h → ℝ, |v ⬝ᵥ (M *ᵥ v)| ≤ β * (v ⬝ᵥ (G *ᵥ v)))
    (hδ : |δ| * β * h ≤ 1 / 2) :
    0 < (G + δ • M).det ∧ (G + δ • M).det ≤ 2 * G.det := by
  classical
  have hG0 : 0 ≤ G := Matrix.nonneg_iff_posSemidef.mpr hG.posSemidef
  set R : Matrix (Fin h) (Fin h) ℝ := CFC.sqrt G with hR
  have hRR : R * R = G := CFC.sqrt_mul_sqrt_self G hG0
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hRsymm : Rᵀ = R := by
    have := hRpsd.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hGsymm : Gᵀ = G := by
    have := hG.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hdetG : 0 < G.det := hG.det_pos
  have hdetGR : G.det = R.det * R.det := by rw [← Matrix.det_mul, hRR]
  have hdetR : R.det ≠ 0 := by
    intro h0
    rw [h0] at hdetGR
    linarith
  have hRunit : IsUnit R.det := isUnit_iff_ne_zero.mpr hdetR
  set Ri : Matrix (Fin h) (Fin h) ℝ := R⁻¹ with hRi
  have hRiR : Ri * R = 1 := Matrix.nonsing_inv_mul R hRunit
  have hRRi : R * Ri = 1 := Matrix.mul_nonsing_inv R hRunit
  have hRisymm : Riᵀ = Ri := by rw [hRi, Matrix.transpose_nonsing_inv, hRsymm]
  set X : Matrix (Fin h) (Fin h) ℝ := G + δ • M with hX
  have hXsymm : Xᵀ = X := by
    rw [hX, Matrix.transpose_add, Matrix.transpose_smul, hGsymm, hMs]
  set A : Matrix (Fin h) (Fin h) ℝ := Ri * X * Ri with hA
  have hXA : X = R * A * R := by
    calc X = (R * Ri) * X * (Ri * R) := by rw [hRRi, hRiR]; simp
      _ = R * A * R := by rw [hA]; simp only [Matrix.mul_assoc]
  have hdetX : X.det = G.det * A.det := by
    conv_lhs => rw [hXA]
    rw [Matrix.det_mul, Matrix.det_mul, hdetGR]; ring
  have hAH : A.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hA, Matrix.transpose_mul,
      Matrix.transpose_mul, hRisymm, hXsymm, Matrix.mul_assoc]
  -- eigenvalue bounds
  set t : ℝ := |δ| * β with ht
  have heig : ∀ i, |hAH.eigenvalues i - 1| ≤ t := by
    intro i
    set v : Fin h → ℝ := ⇑(hAH.eigenvectorBasis i) with hv
    have hev := hAH.eigenvalues_eq i
    have hvv : v ⬝ᵥ v = 1 := by
      have h1 := hAH.eigenvectorBasis.orthonormal.1 i
      have h2 : inner ℝ (hAH.eigenvectorBasis i) (hAH.eigenvectorBasis i) = 1 := by
        rw [real_inner_self_eq_norm_sq, h1]; norm_num
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h2
      simpa [hv, dotProduct_comm] using h2
    set w : Fin h → ℝ := Ri *ᵥ v with hw
    have hRw : R *ᵥ w = v := by
      rw [hw, Matrix.mulVec_mulVec, hRRi, Matrix.one_mulVec]
    have hq : v ⬝ᵥ (A *ᵥ v) = w ⬝ᵥ (X *ᵥ w) := by
      have e1 : A *ᵥ v = Ri *ᵥ (X *ᵥ w) := by
        rw [hA, hw]; simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      have e2 : v ᵥ* Ri = w := by rw [← Matrix.mulVec_transpose, hRisymm]
      rw [e1, Matrix.dotProduct_mulVec, e2]
    have hG1 : w ⬝ᵥ (G *ᵥ w) = 1 := by
      rw [← hRR, ← Matrix.mulVec_mulVec, hRw, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, hRsymm, hRw, hvv]
    have hXw : w ⬝ᵥ (X *ᵥ w) = 1 + δ * (w ⬝ᵥ (M *ᵥ w)) := by
      rw [hX, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, hG1]
      simp
    have hev' : hAH.eigenvalues i = 1 + δ * (w ⬝ᵥ (M *ᵥ w)) := by
      rw [hev, ← hXw, ← hq]
      simp; rfl
    have hMw := hβ w
    rw [hG1, mul_one] at hMw
    rw [hev']
    calc |1 + δ * (w ⬝ᵥ (M *ᵥ w)) - 1| = |δ| * |w ⬝ᵥ (M *ᵥ w)| := by
          rw [add_sub_cancel_left, abs_mul]
      _ ≤ |δ| * β := mul_le_mul_of_nonneg_left hMw (abs_nonneg _)
  have hprod : A.det = ∏ i, hAH.eigenvalues i := by
    simpa using hAH.det_eq_prod_eigenvalues
  have ht0 : ∀ i : Fin h, 0 ≤ t := fun i => (abs_nonneg _).trans (heig i)
  have hth : ∀ i : Fin h, t ≤ 1 / 2 := by
    intro i
    have hh : (1 : ℝ) ≤ h := by exact_mod_cast Nat.succ_le_of_lt i.pos
    have := ht0 i
    nlinarith
  have hlow : ∀ i, 1 - t ≤ hAH.eigenvalues i := fun i => by
    have := (abs_le.mp (heig i)).1; linarith
  have hup : ∀ i, hAH.eigenvalues i ≤ 1 + t := fun i => by
    have := (abs_le.mp (heig i)).2; linarith
  have hApos : 0 < A.det := by
    rw [hprod]
    refine Finset.prod_pos fun i _ => ?_
    have := hth i; have := hlow i; linarith
  have hAle : A.det ≤ 2 := by
    rw [hprod]
    calc ∏ i, hAH.eigenvalues i ≤ ∏ _i : Fin h, Real.exp t := by
          refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
          · have := hth i; have := hlow i; linarith
          · have := Real.add_one_le_exp t; have := hup i; linarith
      _ = Real.exp (t * h) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
          ring_nf
      _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by simpa [ht, mul_assoc] using hδ)
      _ ≤ 2 := exp_half_le_two
  constructor
  · rw [hdetX]; exact mul_pos hdetG hApos
  · rw [hdetX]; nlinarith

end Apery
