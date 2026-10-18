module

public import CatalanLambda.Cert.Final
public import CatalanLambda.Measure.Irrational
public import CatalanLambda.Measure.Measure
public import CatalanLambda.Measure.MeasureOne
public import OAI.NumberTheory.Catalan.Estimates.Contract

@[expose] public section

/-!
# Unconditional results for `λ = G/2 - 5π²/96`

Instantiating the conditional theorems of `CatalanLambda.Measure` with the verified certificate
`CatalanLambda.Cert.certFacts` (`D_cert = 31111/10000`, `c_cert = 68726/10000`), we obtain:

* `λ` is irrational;
* the irrationality exponent of `λ` is at most `M = c_cert (4/(3 (D_cert - 313/105)) + 1) ≈ 77.28`;
* in particular `|λ - p/q| > q^(-78)` for all large `q`, `p` coprime to `q`.
-/

namespace CatalanLambda

open Decay

/-- The exponent `M = c_cert (4 / (3 (D_cert - 313/105)) + 1) ≈ 77.28`. -/
def lambdaMeasureExp : ℚ :=
  (68726 / 10000 : ℚ) * (4 / (3 * ((31111 / 10000 : ℚ) - 313 / 105)) + 1)

theorem lambdaMeasureExp_eq : lambdaMeasureExp = 31682445459 / 409965000 := by
  unfold lambdaMeasureExp; norm_num

theorem lambdaMeasureExp_lt : lambdaMeasureExp < 77.3 := by
  rw [lambdaMeasureExp_eq]; norm_num

theorem lambdaMeasureExp_gt : (77.2 : ℚ) < lambdaMeasureExp := by
  rw [lambdaMeasureExp_eq]; norm_num

theorem certFacts_D : (313 / 105 : ℝ) < Cert.certFacts.Dcert := by
  show (313 / 105 : ℝ) < ((31111 / 10000 : ℚ) : ℝ)
  norm_num

theorem certFacts_c : (0 : ℝ) < (Cert.certFacts.ccert : ℝ) := by
  show (0 : ℝ) < ((68726 / 10000 : ℚ) : ℝ)
  norm_num

/-- **`λ = G/2 - 5π²/96` is irrational.** -/
theorem lambda_irrational_final : Irrational (catalanG / 2 - 5 * Real.pi ^ 2 / 96) :=
  Measure.lambda_irrational Cert.certFacts certFacts_D

/-- **Irrationality measure of `λ`.** For every `e > 0` there is `q₀` such that for all
integers `p` and naturals `q ≥ q₀` with `gcd(p, q) = 1`,
`|λ - p/q| > q^(-(M + e))`, where `M = 31682445459/409965000 ≈ 77.28`. -/
theorem lambda_measure_final {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-((lambdaMeasureExp : ℝ) + e))
        < |(catalanG / 2 - 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := Measure.lambda_measure_one Cert.certFacts certFacts_D certFacts_c he
  refine ⟨q₀, fun p q hc hq => ?_⟩
  have h := H p q hc hq
  have hM : ((Cert.certFacts.ccert : ℝ) *
      (4 / (3 * ((Cert.certFacts.Dcert : ℝ) - 313 / 105)) + 1)) = (lambdaMeasureExp : ℝ) := by
    show ((68726 / 10000 : ℚ) : ℝ) *
      (4 / (3 * (((31111 / 10000 : ℚ) : ℝ) - 313 / 105)) + 1) = (lambdaMeasureExp : ℝ)
    unfold lambdaMeasureExp
    push_cast
    ring
  rwa [hM] at h

/-- **`μ(λ) ≤ 78`**: for all large `q` and all `p` coprime to `q`, `|λ - p/q| > q^(-78)`. -/
theorem lambda_measure_78 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) < |(catalanG / 2 - 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := lambda_measure_final (e := 1 / 2) (by norm_num)
  refine ⟨max q₀ 1, fun p q hc hq => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  have hM : ((lambdaMeasureExp : ℚ) : ℝ) + 1 / 2 ≤ 78 := by
    have h2 : ((lambdaMeasureExp : ℚ) : ℝ) < 773 / 10 := by
      rw [lambdaMeasureExp_eq]; push_cast; norm_num
    linarith
  calc (q : ℝ) ^ (-(78 : ℝ)) ≤ (q : ℝ) ^ (-((lambdaMeasureExp : ℝ) + 1 / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    _ < _ := H p q hc (le_trans (le_max_left _ _) hq)

/-! ### In terms of OpenAI's `catalan` -/

theorem catalanG_eq : catalanG = OAI.InternalCatalan.catalan := rfl

/-- `G - 5π²/48 = 2λ`. -/
theorem catalan_sub_eq_two_lambda :
    OAI.InternalCatalan.catalan - 5 * Real.pi ^ 2 / 48
      = 2 * (OAI.InternalCatalan.catalan / 2 - 5 * Real.pi ^ 2 / 96) := by ring

theorem lambda_irrational_catalan :
    Irrational (OAI.InternalCatalan.catalan / 2 - 5 * Real.pi ^ 2 / 96) := by
  rw [← catalanG_eq]; exact lambda_irrational_final

/-- `G - 5π²/48` is irrational. -/
theorem catalan_sub_irrational : Irrational (OAI.InternalCatalan.catalan - 5 * Real.pi ^ 2 / 48) := by
  rw [catalan_sub_eq_two_lambda]
  have h := lambda_irrational_catalan.ratCast_mul (q := 2) (by norm_num)
  push_cast at h
  exact h

theorem lambda_measure_78_catalan :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ))
        < |(OAI.InternalCatalan.catalan / 2 - 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| :=
  lambda_measure_78

end CatalanLambda

