module

public import CatalanLambda.Mirror.Measure
public import CatalanLambda.Mirror.Lemma3

@[expose] public section

/-!
# Irrationality measure of `λ'` with Lemma 3: `μ(λ') ≤ c (4/(3η) + 1)`
-/

namespace CatalanLambda.Mirror

open CatalanLambda.Decay

theorem hex_one (a b : ℝ) (ha : 0 < a) (hab : a + 1 < b) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      ∃ ℓ h : ℕ, a * Real.log q < ℓ ∧ (ℓ : ℝ) ≤ b * Real.log q ∧ 3 * ℓ ≤ 4 * h + 4 ∧
        h ≤ ℓ - 1 ∧ Pbar h ((p : ℚ) / (q : ℚ)) ≠ 0 := by
  obtain ⟨q₁, hq₁⟩ := exists_prime_window_sq1 a b ha hab
  refine ⟨max q₁ ⌈Real.exp (14 / a)⌉₊, fun p q hcop hq => ?_⟩
  obtain ⟨ℓ, hp, h3, hl1, hl2, hbad⟩ := hq₁ q (le_trans (le_max_left _ _) hq)
  have hqe : Real.exp (14 / a) ≤ q :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hq)
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hqe
  have hq0 : 0 < q := by exact_mod_cast hqpos
  have hL : 14 / a ≤ Real.log q := (Real.le_log_iff_exp_le hqpos).2 hqe
  have h8 : (14 : ℝ) ≤ a * Real.log q := by
    rw [div_le_iff₀ ha] at hL; linarith
  have h13 : 13 ≤ ℓ := by
    have : (13 : ℝ) < ℓ := by linarith
    have : 13 < ℓ := by exact_mod_cast this
    omega
  have : Fact ℓ.Prime := ⟨hp⟩
  by_cases hdv : ℓ ∣ q
  · exact ⟨ℓ, (3 * ℓ - 3) / 4, hl1, hl2, by omega, by omega,
      lemma3_pq ℓ h3 h13 p q hq0 hcop hdv hbad⟩
  · obtain ⟨h, hh1, hh2, hP⟩ := exists_h_nonvanishing ℓ h3 h13 p (q : ℤ) (by simpa using hdv)
    exact ⟨ℓ, h, hl1, hl2, by omega, hh2, by simpa using hP⟩

/-- **Irrationality measure of `λ'` (with Lemma 3).**  Under `CertFacts` with `D_cert > 313/105`
and `c_cert > 0`: for every `e > 0`, for all large `q` and all integers `p` coprime to `q`,
`|λ' - p/q| > q^{-(M + e)}` with `M = c_cert (4/(3η) + 1)`, `η = D_cert - 313/105`. -/
theorem lambda_mirror_measure_one {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) (hD : (313 / 105 : ℝ) < F.Dcert) (hc : 0 < (F.ccert : ℝ))
    {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-((F.ccert : ℝ) * (4 / (3 * ((F.Dcert : ℝ) - 313 / 105)) + 1) + e))
        < |(catalanG / 2 + 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  rw [← lamB_eq]
  exact measure_core F hD hc 1 one_pos (fun p q => Nat.Coprime p.natAbs q) hex_one he

end CatalanLambda.Mirror
