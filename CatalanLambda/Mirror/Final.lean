module

public import CatalanLambda.Final
public import CatalanLambda.Mirror.MeasureOne

@[expose] public section

/-!
# Unconditional results for the mirror constant `λ' = G/2 + 5π²/96`

Instantiating the conditional mirror theorems with the verified certificate
`CatalanLambda.Cert.certFacts` (`D_cert = 31111/10000`, `c_cert = 68726/10000`; the SAME
certificate as for `λ = G/2 - 5π²/96`, since the function `g` does not depend on the atoms'
positions modulo `1`), we obtain:

* `λ'` is irrational, hence `G + 5π²/48 = 2 λ'` is irrational;
* the irrationality exponent of `λ'` is at most `M = c_cert (4/(3 (D_cert - 313/105)) + 1) ≈ 77.28`
  (the same `M` as for `λ`);
* in particular `|λ' - p/q| > q^(-78)` for all large `q`, `p` coprime to `q`.
-/

namespace CatalanLambda.Mirror

open CatalanLambda.Decay

/-- **`λ' = G/2 + 5π²/96` is irrational.** -/
theorem lambda_mirror_irrational_final : Irrational (catalanG / 2 + 5 * Real.pi ^ 2 / 96) :=
  lambda_mirror_irrational Cert.certFacts certFacts_D

/-- **Irrationality measure of `λ'`.** For every `e > 0` there is `q₀` such that for all
integers `p` and naturals `q ≥ q₀` with `gcd(p, q) = 1`,
`|λ' - p/q| > q^(-(M + e))`, where `M = 31682445459/409965000 ≈ 77.28`. -/
theorem lambda_mirror_measure_final {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-((lambdaMeasureExp : ℝ) + e))
        < |(catalanG / 2 + 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := lambda_mirror_measure_one Cert.certFacts certFacts_D certFacts_c he
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

/-- **`μ(λ') ≤ 78`**: for all large `q` and all `p` coprime to `q`, `|λ' - p/q| > q^(-78)`. -/
theorem lambda_mirror_measure_78 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) < |(catalanG / 2 + 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := lambda_mirror_measure_final (e := 1 / 2) (by norm_num)
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

/-- `G + 5π²/48 = 2 λ'`. -/
theorem catalan_add_eq_two_lambda_mirror :
    OAI.InternalCatalan.catalan + 5 * Real.pi ^ 2 / 48
      = 2 * (OAI.InternalCatalan.catalan / 2 + 5 * Real.pi ^ 2 / 96) := by ring

theorem lambda_mirror_irrational_catalan :
    Irrational (OAI.InternalCatalan.catalan / 2 + 5 * Real.pi ^ 2 / 96) := by
  rw [← catalanG_eq]; exact lambda_mirror_irrational_final

/-- `G + 5π²/48` is irrational. -/
theorem catalan_add_irrational : Irrational (OAI.InternalCatalan.catalan + 5 * Real.pi ^ 2 / 48) := by
  rw [catalan_add_eq_two_lambda_mirror]
  have h := lambda_mirror_irrational_catalan.ratCast_mul (q := 2) (by norm_num)
  push_cast at h
  exact h

theorem lambda_mirror_measure_78_catalan :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ))
        < |(OAI.InternalCatalan.catalan / 2 + 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| :=
  lambda_mirror_measure_78

end CatalanLambda.Mirror
