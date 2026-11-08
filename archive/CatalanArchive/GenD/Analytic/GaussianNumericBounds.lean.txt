module

public import CatalanMeasure.GenD.Analytic.GaussianCertificate

@[expose] public section
namespace CatalanMeasure.GenD.Analytic.GaussianNumericBounds
open Polynomial GaussianHorner GaussianCertificate
noncomputable section

/-- A homogeneous integer Horner witness bounds the actual derivative on a disk. -/
theorem derivative_norm_le_of_checks (cs : List (ℤ × ℤ)) (U : List ℤ)
    (hU : normsOK (weightedPairs 1 cs.tail) U = true)
    (x den num : ℤ) (hden : 0 < den) (hx : 0 ≤ x)
    (hnum : positiveHorner U x den = num) {B : ℝ}
    (hbound : (num : ℝ) * (den : ℝ) ≤ (den : ℝ) ^ U.length * B)
    (z : ℂ) (hz : ‖z‖ ≤ (x : ℝ) / (den : ℝ)) :
    ‖(polynomialOfPairs cs).derivative.eval z‖ ≤ B := by
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have hxR : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hh := positiveHorner_sound U x den hden.ne'
  rw [hnum] at hh
  have hH : normHorner (U.map (fun (a : ℤ) => (a : ℝ))) ((x : ℝ) / (den : ℝ)) ≤ B := by
    rw [hh] at hbound
    nlinarith [pow_pos hd U.length]
  exact (polynomialOfPairs_derivative_norm_le (normsOK_sound hU) (by positivity) z hz).trans hH

theorem evalPairs_re_lower (a : ℤ × ℤ) (cs : List (ℤ × ℤ)) (U : List ℝ)
    (hU : List.Forall₂ (fun b u => ‖castPair b‖ ≤ u) cs U)
    {r : ℝ} (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ r) :
    (a.1 : ℝ) - r * normHorner U r ≤ (evalPairs (a :: cs) z).re := by
  have ht := evalPairs_norm_le hU hr z hz
  have hn : ‖z * evalPairs cs z‖ ≤ r * normHorner U r := by
    rw [norm_mul]
    exact mul_le_mul hz ht (norm_nonneg _) hr
  have hl' : -(r * normHorner U r) ≤ (z * evalPairs cs z).re := by
    have hh := (Complex.abs_re_le_norm (z * evalPairs cs z)).trans hn
    have hneg := neg_abs_le (z * evalPairs cs z).re
    linarith
  have hcast : (castPair a).re = (a.1 : ℝ) := by simp [castPair]
  change (a.1 : ℝ) - r * normHorner U r ≤ (castPair a + z * evalPairs cs z).re
  rw [Complex.add_re, hcast]
  linarith

end
end CatalanMeasure.GenD.Analytic.GaussianNumericBounds
#print axioms CatalanMeasure.GenD.Analytic.GaussianNumericBounds.derivative_norm_le_of_checks
#print axioms CatalanMeasure.GenD.Analytic.GaussianNumericBounds.evalPairs_re_lower
