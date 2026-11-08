module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/InverseImageCircle.lean
Original SHA256: 733c40b9679d7d3bce4b04bfedd8dbe6f062c77621fbc47f31c6bdf6cd0e74b1
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Signed.Davis.InverseImageNodes

@[expose] public section

/-!
# Scaling a fixed-degree polynomial circle certificate

The certificate is stated using integer powers. Raising the desired circle
bound to the fixed positive degree `m` avoids fractional powers and complex
logarithms. The ceiling in the Chebyshev degree costs one fixed factor.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Polynomial.Chebyshev Finset Set

noncomputable section

def inverseImageDegree (J m : ℕ) : ℕ := (J + m - 1) / m

theorem inverseImageDegree_bounds (J : ℕ) {m : ℕ} (hm : 0 < m) :
    J ≤ inverseImageDegree J m * m ∧
      inverseImageDegree J m * m ≤ J + m - 1 := by
  have hrem := Nat.mod_lt (J + m - 1) hm
  have hid := Nat.mod_add_div (J + m - 1) m
  rw [Nat.mul_comm m] at hid
  dsimp only [inverseImageDegree]
  omega

theorem inverseImageDegree_pos {J m : ℕ} (hJ : 0 < J) (hm : 0 < m) :
    0 < inverseImageDegree J m := by
  have hlow := (inverseImageDegree_bounds J hm).1
  apply Nat.pos_of_ne_zero
  intro hz
  rw [hz, zero_mul] at hlow
  omega

theorem inverseImageSurplus_lt (J : ℕ) {m : ℕ} (hm : 0 < m) :
    inverseImageDegree J m * m - J < m := by
  have hb := inverseImageDegree_bounds J hm
  omega

/-- A joint certificate for `P` and the filter transfers to every Chebyshev
composition whose degree exceeds `d*N` by at most one block of size `m`.
`C` bounds `2*|P(z)|+1` on the fixed circle and has no exponential cost. -/
theorem inverseImagePolynomial_circle_le {p : ℝ[X]} {d h m N K : ℕ}
    (hm : 0 < m) (hK : K * m ≤ d * N + m)
    {radius C wc : ℝ}
    (hC : ∀ z : ℂ, ‖z‖ = radius →
      2 * ‖(p.map (algebraMap ℝ ℂ)).eval z‖ + 1 ≤ C)
    (hcert : ∀ z : ℂ, ‖z‖ = radius →
      (2 * ‖(p.map (algebraMap ℝ ℂ)).eval z‖ + 1) ^ d *
        ‖(1 : ℂ) - z‖ ^ (h * m) ≤ Real.exp ((m : ℝ) * wc))
    (z : ℂ) (hz : ‖z‖ = radius) :
    ‖((inverseImagePolynomial p K).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1 : ℂ) - z‖ ^ (h * N) ≤ C * Real.exp (wc * N) := by
  let A : ℝ := 2 * ‖(p.map (algebraMap ℝ ℂ)).eval z‖ + 1
  let F : ℝ := ‖(1 : ℂ) - z‖
  have hA1 : 1 ≤ A := by
    dsimp [A]
    linarith only [norm_nonneg ((p.map (algebraMap ℝ ℂ)).eval z)]
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hF0 : 0 ≤ F := norm_nonneg _
  have hAC : A ≤ C := hC z hz
  have hC0 : 0 ≤ C := hA0.trans hAC
  have hbase : A ^ d * F ^ (h * m) ≤ Real.exp ((m : ℝ) * wc) := hcert z hz
  have hnorm : ‖((inverseImagePolynomial p K).map (algebraMap ℝ ℂ)).eval z‖ ≤ A ^ K :=
    inverseImagePolynomial_norm_le K z
  have hexp : (Real.exp ((m : ℝ) * wc)) ^ N = (Real.exp (wc * N)) ^ m := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  have hmain :
      (‖((inverseImagePolynomial p K).map (algebraMap ℝ ℂ)).eval z‖ * F ^ (h * N)) ^ m ≤
        (C * Real.exp (wc * N)) ^ m := by
    calc
      _ ≤ (A ^ K * F ^ (h * N)) ^ m :=
        pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right hnorm (pow_nonneg hF0 _)) m
      _ = A ^ (K * m) * F ^ (h * m * N) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        congr 1
        congr 1
        ring
      _ ≤ A ^ (d * N + m) * F ^ (h * m * N) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1 hK) (pow_nonneg hF0 _)
      _ = A ^ m * (A ^ d * F ^ (h * m)) ^ N := by
        rw [pow_add, mul_pow, ← pow_mul, ← pow_mul]
        ring
      _ ≤ C ^ m * (Real.exp ((m : ℝ) * wc)) ^ N :=
        mul_le_mul (pow_le_pow_left₀ hA0 hAC m)
          (pow_le_pow_left₀ (by positivity) hbase N)
          (by positivity) (pow_nonneg hC0 _)
      _ = (C * Real.exp (wc * N)) ^ m := by rw [hexp, mul_pow]
  exact le_of_pow_le_pow_left₀ (Nat.ne_of_gt hm) (by positivity) hmain

end
end Analytic
end CatalanMeasure.GenD

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.GenD.Analytic.inverseImageDegree
#print axioms CatalanMeasure.GenD.Analytic.inverseImageDegree_bounds
#print axioms CatalanMeasure.GenD.Analytic.inverseImageDegree_pos
#print axioms CatalanMeasure.GenD.Analytic.inverseImageSurplus_lt
#print axioms CatalanMeasure.GenD.Analytic.inverseImagePolynomial_circle_le
