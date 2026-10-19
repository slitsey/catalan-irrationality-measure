module

public import CatalanCore.Arith.Hybrid.LemmaE.MatCong
public import CatalanCore.Arith.Hybrid.LemmaE.TCore

@[expose] public section

/-!
# The block-scaling lemma (DQ, "AX Lemma 1 generalised")

For `D = diag(p^{d i})` and `Ã = D A D`:
* `g = det Ã`, `N = D adj(Ã) D` satisfy `A N = g • 1` and `p^s det A = g` with `s = 2 ∑ d`;
* if `Ã` is integral and congruent to an integral `M` whose determinant is primitive, then `g` is
  primitive (`gn p g = 1`).
These are exactly the inputs `g, N, s` of `tcore`.
-/

open Polynomial Finset Matrix

namespace CatalanCore.Arith.Hybrid.LemmaE

variable (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The diagonal scaling matrix `diag(p^{d i})`. -/
noncomputable def scl (d : ι → ℕ) : Matrix ι ι ℚ[X] := Matrix.diagonal fun i => C ((p : ℚ) ^ d i)

/-- The rescaled block `Ã = D A D`. -/
noncomputable def Atil (d : ι → ℕ) (A : Matrix ι ι ℚ[X]) : Matrix ι ι ℚ[X] :=
  scl p d * A * scl p d

lemma prod_scl (d : ι → ℕ) : (∏ i, C ((p : ℚ) ^ d i)) = C ((p : ℚ) ^ (∑ i, d i)) := by
  rw [← Finset.prod_pow_eq_pow_sum, map_prod]

lemma scl_unit (d : ι → ℕ) : IsUnit (scl p d) := by
  unfold scl
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, prod_scl]
  have : ((p : ℚ) ^ (∑ i, d i)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  exact (Polynomial.isUnit_C).mpr (IsUnit.mk0 _ this)

lemma Atil_apply (d : ι → ℕ) (A : Matrix ι ι ℚ[X]) (i j : ι) :
    Atil p d A i j = C ((p : ℚ) ^ d i) * A i j * C ((p : ℚ) ^ d j) := by
  simp [Atil, scl, Matrix.mul_apply, Matrix.diagonal_apply]

/-- `N = D adj(Ã) D`. -/
noncomputable def Nmat (d : ι → ℕ) (A : Matrix ι ι ℚ[X]) : Matrix ι ι ℚ[X] :=
  scl p d * (Atil p d A).adjugate * scl p d

theorem AN_eq (d : ι → ℕ) (A : Matrix ι ι ℚ[X]) :
    A * Nmat p d A = (Atil p d A).det • (1 : Matrix ι ι ℚ[X]) := by
  have hu := scl_unit p d
  have h1 : (Atil p d A) * (Atil p d A).adjugate = (Atil p d A).det • 1 :=
    Matrix.mul_adjugate _
  have h2 : scl p d * (A * Nmat p d A) = scl p d * ((Atil p d A).det • 1) := by
    have : scl p d * (A * Nmat p d A) = (Atil p d A * (Atil p d A).adjugate) * scl p d := by
      simp only [Atil, Nmat, Matrix.mul_assoc]
    rw [this, h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  exact (hu.mul_right_inj).mp h2

theorem det_Atil (d : ι → ℕ) (A : Matrix ι ι ℚ[X]) :
    (Atil p d A).det = C ((p : ℚ) ^ (2 * ∑ i, d i)) * A.det := by
  unfold Atil scl
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_scl, two_mul, pow_add, map_mul]
  ring

/-- `det Ã` is primitive once `Ã` is integral and congruent to an integral `M` with primitive
determinant. -/
theorem prim_det_Atil (d : ι → ℕ) (A M : Matrix ι ι ℚ[X])
    (hI : ∀ i j, Int1 p (Atil p d A i j)) (hM : ∀ i j, Int1 p (M i j))
    (hc : ∀ i j, Cng p (Atil p d A i j) (M i j)) (hprim : gn p M.det = 1) :
    gn p (Atil p d A).det = 1 :=
  Cng.gn_eq_one (det_cng hI hM hc) hprim

/-- **T-route criterion with block scaling.**  The clean block `A` of `Full`, rescaled by
`p^{d}`, is integral and congruent to an integral `M` of primitive determinant; the entries of
`g T = g D - C N B` are `p^{-b}`-integral.  Then `v_p(det Full) ≥ -(2 ∑ d + m b)`. -/
theorem tcore_scaled {κ : Type} [Fintype κ] [DecidableEq κ]
    (Full : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X]) (d : ι → ℕ) (M : Matrix ι ι ℚ[X])
    (hI : ∀ i j, Int1 p (Atil p d Full.toBlocks₁₁ i j)) (hM : ∀ i j, Int1 p (M i j))
    (hc : ∀ i j, Cng p (Atil p d Full.toBlocks₁₁ i j) (M i j)) (hprim : gn p M.det = 1)
    (b : ℕ) (hT : ∀ z y, GLE p b (Tscaled (Atil p d Full.toBlocks₁₁).det Full.toBlocks₁₁
        Full.toBlocks₁₂ Full.toBlocks₂₁ Full.toBlocks₂₂ (Nmat p d Full.toBlocks₁₁) z y)) :
    GLE p (Fintype.card κ * b + 2 * ∑ i, d i) Full.det := by
  refine tcore p Full _ (prim_det_Atil p d _ M hI hM hc hprim) (Nmat p d Full.toBlocks₁₁)
    (AN_eq p d _) (2 * ∑ i, d i) ?_ b hT
  rw [← det_Atil]

theorem NA_eq (d : ι → ℕ) (A : Matrix ι ι ℚ[X]) :
    Nmat p d A * A = (Atil p d A).det • (1 : Matrix ι ι ℚ[X]) := by
  have hu := scl_unit p d
  have h1 : (Atil p d A).adjugate * (Atil p d A) = (Atil p d A).det • 1 :=
    Matrix.adjugate_mul _
  have h2 : (Nmat p d A * A) * scl p d = ((Atil p d A).det • 1) * scl p d := by
    have : (Nmat p d A * A) * scl p d = scl p d * ((Atil p d A).adjugate * Atil p d A) := by
      simp only [Atil, Nmat, Matrix.mul_assoc]
    rw [this, h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one]
  exact (hu.mul_left_inj).mp h2

end CatalanCore.Arith.Hybrid.LemmaE
