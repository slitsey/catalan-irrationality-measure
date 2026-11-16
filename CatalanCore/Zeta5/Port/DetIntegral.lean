module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CatalanCore.Zeta5.Port.Andreief
public import CatalanCore.Zeta5.Port.Positivity

@[expose] public section

/-! Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/DetIntegral.lean (Moritz Firsching); changes: module conversion (module/public import/expose), imports renamed to CatalanCore.Zeta5.Port. -/

/-!
# The Hankel determinant as a multiple integral, (6.10)

`Δ_K(ζ(5)) = (1/h!) ∫_{(0,∞)^h} det(V(y))² ∏ᵢ ν(yᵢ) dy`, where `V(y)` is the Vandermonde matrix
of `y₁², …, y_h²` and `ν(y) = D_N(y²)^6 / D_K(y²) · w(y)`.
-/

open MeasureTheory Set Finset Polynomial

namespace Apery

/-- The measure `dy` on `(0, ∞)`. -/
noncomputable abbrev μpos : Measure ℝ := volume.restrict (Ioi 0)

/-- **(6.10)**: the Hankel determinant as a multiple integral. -/
theorem Δ_eq_integral (n : ℕ) :
    aeval zeta5 (Δ n) = (1 / ((37 * n).factorial : ℝ)) *
      ∫ x : Fin (37 * n) → ℝ, (Matrix.vandermonde fun j => x j ^ 2).det ^ 2 * ∏ j, ν n (x j)
        ∂(Measure.pi fun _ : Fin (37 * n) => μpos) := by
  -- the matrix `G_K(ζ(5))` has entries `∫ (y²)^i · ((y²)^j ν(y)) dy`
  have hdet : aeval zeta5 (Δ n) = ((G n).map (aeval zeta5)).det := by
    have := RingHom.map_det (aeval zeta5 : ℚ[X] →ₐ[ℚ] ℝ).toRingHom (G n)
    simpa [Δ, RingHom.mapMatrix_apply] using this
  set f : Fin (37 * n) → ℝ → ℝ := fun i y => (y ^ 2) ^ (i : ℕ) with hf
  set g : Fin (37 * n) → ℝ → ℝ := fun j y => (y ^ 2) ^ (j : ℕ) * ν n y with hg
  have hentry : (G n).map (aeval zeta5) = Matrix.of fun i j => ∫ y, f i y * g j y ∂μpos := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, G, hf, hg]
    rw [(moment_rep _ _).2]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    rw [integrand_eq]; ring
  have hfg : ∀ i j, Integrable (fun y => f i y * g j y) μpos := by
    intro i j
    have := (moment_rep (40 * n) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ)))).1
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    simp only [hf, hg]; rw [integrand_eq]; ring
  rw [hdet, hentry, andreief f g hfg]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  -- `det (f i (x j)) = det Vᵀ` and `det (g i (x j)) = (∏ ν) det Vᵀ`
  have h1 : (Matrix.of fun i j => f i (x j)).det = (Matrix.vandermonde fun j => x j ^ 2).det := by
    rw [← Matrix.det_transpose (Matrix.vandermonde _)]
    refine congrArg Matrix.det ?_
    ext i j; simp [hf, Matrix.vandermonde, Matrix.transpose_apply]
  have h2 : (Matrix.of fun i j => g i (x j)).det =
      (∏ j, ν n (x j)) * (Matrix.vandermonde fun j => x j ^ 2).det := by
    have : (Matrix.of fun i j => g i (x j)) =
        Matrix.of fun i j => ν n (x j) * (Matrix.of fun i j => f i (x j)) i j := by
      ext i j; simp [hf, hg]; ring
    rw [this, Matrix.det_mul_row, h1]
  show (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det =
    (Matrix.vandermonde fun j => x j ^ 2).det ^ 2 * ∏ j, ν n (x j)
  rw [h1, h2]; ring

end Apery
