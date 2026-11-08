module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/PolynomialNorm.lean
Original SHA256: 454bf32d50c0919c921e5e1eaad730dace03d5bc44966b23e073d7bcbf1f2901
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic

@[expose] public section

/-!
# Rational Horner certificates for polynomial norms

The coefficient data are rational. The norm estimate is the triangle
inequality, proved once by induction; checking its rational right side does
not use floating-point arithmetic.
-/

namespace CatalanMeasure.Refinement

open Polynomial

noncomputable def polynomialFromCoeffs : List ℚ → ℚ[X]
  | [] => 0
  | a :: as => C a + X * polynomialFromCoeffs as

def hornerNormBound : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: as, r => |a| + r * hornerNormBound as r

theorem hornerNormBound_nonneg (as : List ℚ) {r : ℚ} (hr : 0 ≤ r) :
    0 ≤ hornerNormBound as r := by
  induction as with
  | nil => simp [hornerNormBound]
  | cons a as ih =>
      exact add_nonneg (abs_nonneg a) (mul_nonneg hr ih)

theorem norm_eval_polynomialFromCoeffs_le (as : List ℚ) {r : ℚ}
    (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ (r : ℝ)) :
    ‖((polynomialFromCoeffs as).map (algebraMap ℚ ℂ)).eval z‖ ≤
      (hornerNormBound as r : ℝ) := by
  induction as with
  | nil => simp [polynomialFromCoeffs, hornerNormBound]
  | cons a as ih =>
      simp only [polynomialFromCoeffs, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X, eval_add, eval_mul, eval_C, eval_X]
      calc
        _ ≤ ‖(a : ℂ)‖ + ‖z‖ *
            ‖((polynomialFromCoeffs as).map (algebraMap ℚ ℂ)).eval z‖ := by
              simpa only [norm_mul, eq_ratCast] using norm_add_le (a : ℂ)
                (z * ((polynomialFromCoeffs as).map (algebraMap ℚ ℂ)).eval z)
        _ ≤ |(a : ℝ)| + (r : ℝ) * (hornerNormBound as r : ℝ) := by
              rw [Complex.norm_ratCast]
              gcongr
        _ = (hornerNormBound (a :: as) r : ℝ) := by
              simp [hornerNormBound]

def expTaylorRat (x : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ i / (Nat.factorial i : ℚ)

theorem expTaylorRat_le_exp {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    (expTaylorRat x n : ℝ) ≤ Real.exp (x : ℝ) := by
  have hxR : (0 : ℝ) ≤ x := by exact_mod_cast hx
  simpa [expTaylorRat] using Real.sum_le_exp_of_nonneg hxR n

/-- A dyadic factor removes the large integer part before a short Taylor
lower bound. The finite premise is a rational comparison. -/
theorem rational_le_exp_of_binary_taylor (A x t : ℚ) (j n : ℕ)
    (ht : 0 ≤ t)
    (hdecomp : (j : ℝ) * Real.log 2 + (t : ℝ) ≤ (x : ℝ))
    (hfinite : A ≤ (2 : ℚ) ^ j * expTaylorRat t n) :
    (A : ℝ) ≤ Real.exp (x : ℝ) := by
  have hf : (A : ℝ) ≤ (2 : ℝ) ^ j * (expTaylorRat t n : ℝ) := by
    exact_mod_cast hfinite
  have hp : (2 : ℝ) ^ j = Real.exp ((j : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    (A : ℝ) ≤ 2 ^ j * (expTaylorRat t n : ℝ) := hf
    _ ≤ 2 ^ j * Real.exp (t : ℝ) :=
      mul_le_mul_of_nonneg_left (expTaylorRat_le_exp ht n) (by positivity)
    _ = Real.exp ((j : ℝ) * Real.log 2 + (t : ℝ)) := by
      rw [hp, Real.exp_add]
    _ ≤ Real.exp (x : ℝ) := Real.exp_le_exp.mpr hdecomp

/-- A norm bound for a filtered polynomial gives the circle hypothesis needed
by the inverse-image quadrature theorem. -/
theorem weighted_circle_of_filtered_norm (p : ℂ[X])
    (d h m k ell : ℕ) (r M wc : ℝ) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hdegree : h * m = d * k + ell)
    (hsize : ∀ z : ℂ, ‖z‖ = r → ‖(p * (1 - X) ^ k).eval z‖ ≤ M)
    (hfinite : (2 * M + (r + 1) ^ k) ^ d * (r + 1) ^ ell ≤ Real.exp (m * wc)) :
    ∀ z : ℂ, ‖z‖ = r →
      (2 * ‖p.eval z‖ + 1) ^ d * ‖(1 : ℂ) - z‖ ^ (h * m) ≤
        Real.exp (m * wc) := by
  intro z hz
  have ht : ‖(1 : ℂ) - z‖ ≤ r + 1 := by
    simpa [hz, add_comm] using norm_sub_le (1 : ℂ) z
  have hq : ‖(p * (1 - X) ^ k).eval z‖ =
      ‖p.eval z‖ * ‖(1 : ℂ) - z‖ ^ k := by
    simp only [eval_mul, eval_pow, eval_sub, eval_one, eval_X, norm_mul, norm_pow]
  have hp := hsize z hz
  rw [hq] at hp
  calc
    _ = (2 * (‖p.eval z‖ * ‖(1 : ℂ) - z‖ ^ k) +
          ‖(1 : ℂ) - z‖ ^ k) ^ d * ‖(1 : ℂ) - z‖ ^ ell := by
            rw [hdegree, pow_add, Nat.mul_comm d k, pow_mul, ← mul_assoc, ← mul_pow]
            congr 2
            ring
    _ ≤ (2 * M + (r + 1) ^ k) ^ d * (r + 1) ^ ell := by
      gcongr
    _ ≤ Real.exp (m * wc) := hfinite

end CatalanMeasure.Refinement

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.Refinement.polynomialFromCoeffs
#print axioms CatalanMeasure.Refinement.hornerNormBound
#print axioms CatalanMeasure.Refinement.hornerNormBound_nonneg
#print axioms CatalanMeasure.Refinement.norm_eval_polynomialFromCoeffs_le
#print axioms CatalanMeasure.Refinement.expTaylorRat
#print axioms CatalanMeasure.Refinement.expTaylorRat_le_exp
#print axioms CatalanMeasure.Refinement.rational_le_exp_of_binary_taylor
#print axioms CatalanMeasure.Refinement.weighted_circle_of_filtered_norm
