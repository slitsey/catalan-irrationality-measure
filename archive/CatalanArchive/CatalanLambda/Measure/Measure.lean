module

public import CatalanArchive.CatalanLambda.Measure.MeasureCore

@[expose] public section

/-!
# Irrationality measure of `λ` without Lemma 3: `μ(λ) ≤ c (4/(3η) + 2)`
-/

namespace CatalanLambda.Measure

open CatalanLambda.Decay

/-- Existence of the data required by `measure_core` with `s = 2`: a prime `ℓ ≡ 3 (4)` in
`(a log q, b log q]` not dividing `q`, and then nonvanishing at one of the three indices. -/
theorem hex_two (a b : ℝ) (ha : 0 < a) (hab : a + 2 < b) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), True → q₀ ≤ q →
      ∃ ℓ h : ℕ, a * Real.log q < ℓ ∧ (ℓ : ℝ) ≤ b * Real.log q ∧ (3 * ℓ - 1) / 4 ≤ h ∧
        h ≤ ℓ - 1 ∧ CatalanLambda.P h ((p : ℚ) / (q : ℚ)) ≠ 0 := by
  obtain ⟨q₁, hq₁⟩ := exists_prime_window a b ha hab
  refine ⟨max q₁ ⌈Real.exp (8 / a)⌉₊, fun p q _ hq => ?_⟩
  obtain ⟨ℓ, hp, h3, hl1, hl2, hnd⟩ := hq₁ q (le_trans (le_max_left _ _) hq)
  have hqe : Real.exp (8 / a) ≤ q :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hq)
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hqe
  have hL : 8 / a ≤ Real.log q := (Real.le_log_iff_exp_le hqpos).2 hqe
  have h8 : (8 : ℝ) ≤ a * Real.log q := by
    rw [div_le_iff₀ ha] at hL; linarith
  have h7 : 7 ≤ ℓ := by
    have : (7 : ℝ) < ℓ := by linarith
    have : 7 < ℓ := by exact_mod_cast this
    omega
  have : Fact ℓ.Prime := ⟨hp⟩
  obtain ⟨h, hh1, hh2, hP⟩ := exists_h_nonvanishing ℓ h3 h7 p (q : ℤ) (by simpa using hnd)
  exact ⟨ℓ, h, hl1, hl2, hh1, hh2, by simpa using hP⟩

/-- **Irrationality measure (without Lemma 3).**  Under `CertFacts` with `D_cert > 313/105` and
`c_cert > 0`: for every `e > 0`, for all large `q` and all integers `p`,
`|λ - p/q| > q^{-(M + e)}` with `M = c_cert (4/(3η) + 2)`, `η = D_cert - 313/105`.
Equivalently `μ(λ) ≤ c_cert (4/(3η) + 2)`. -/
theorem lambda_measure_two {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) (hD : (313 / 105 : ℝ) < F.Dcert) (hc : 0 < (F.ccert : ℝ))
    {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-((F.ccert : ℝ) * (4 / (3 * ((F.Dcert : ℝ) - 313 / 105)) + 2) + e))
        < |(catalanG / 2 - 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  rw [← lamS_eq]
  obtain ⟨q₀, H⟩ := measure_core F hD hc 2 two_pos (fun _ _ => True) hex_two he
  exact ⟨q₀, fun p q hq => H p q trivial hq⟩

end CatalanLambda.Measure
