module

public import CatalanCore.Arith.Hybrid.Tropical
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# UF member package: the scaled gauge `X = U/p²`

The Smith-layer formulas of `smith-deletion/THEOREM.md` live in the scaled gauge: the matrix is
`Ψ(U) = Φ(U/p²)`, entrywise `f ↦ f.comp (C (p²)⁻¹ * X)` (`scaleU p`).  A price in that gauge is a
price in the original variable: the `U^i` coefficient is the `X^i` coefficient times `p^(-2i)`
(`gle_of_gle_scaleU`), and the substitution commutes with determinants and minors
(`det_map_scaleU`).
-/

open Polynomial CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Uniform.Content.UFMember

variable (p : ℕ) [Fact p.Prime]

/-- The substitution `X ↦ X/p²`. -/
noncomputable def scaleU : ℚ[X] →+* ℚ[X] := Polynomial.compRingHom (C (((p : ℚ) ^ 2)⁻¹) * X)

lemma scaleU_coeff (f : ℚ[X]) (i : ℕ) :
    (scaleU p f).coeff i = f.coeff i * (((p : ℚ) ^ 2)⁻¹) ^ i := by
  simp [scaleU]

variable {p}

/-- **Gauge transfer.**  A `p`-denominator bound in the scaled gauge is one in `X`. -/
theorem gle_of_gle_scaleU {B : ℕ} {f : ℚ[X]} (h : GLE p B (scaleU p f)) : GLE p B f := by
  intro i
  have hi := h i
  rw [scaleU_coeff] at hi
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e : (p : ℚ) ^ B * f.coeff i =
      ((p : ℚ) ^ B * (f.coeff i * (((p : ℚ) ^ 2)⁻¹) ^ i)) * (((p ^ (2 * i) : ℕ) : ℤ) : ℚ) := by
    push_cast
    rw [inv_pow, ← pow_mul]
    field_simp
  rw [e]
  exact (LocRing p).mul_mem hi (int_mem_locRing (ℓ := p) _)

/-- The substitution commutes with determinants. -/
theorem det_map_scaleU {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ[X]) :
    (M.map (scaleU p)).det = scaleU p M.det :=
  (RingHom.map_det (scaleU p) M).symm

/-- A scaled-gauge price for a minor of `Ψ = Φ(U/p²)` is a price for the minor of `Φ`. -/
theorem gle_submatrix_of_scaleU {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {B : ℕ} (M : Matrix ι ι ℚ[X]) (e₁ e₂ : κ → ι)
    (h : GLE p B ((M.map (scaleU p)).submatrix e₁ e₂).det) :
    GLE p B (M.submatrix e₁ e₂).det := by
  apply gle_of_gle_scaleU
  rw [← det_map_scaleU]
  exact h

end CatalanCore.Uniform.Content.UFMember
