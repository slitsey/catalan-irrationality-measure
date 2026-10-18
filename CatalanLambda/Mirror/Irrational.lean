module

public import CatalanLambda.Mirror.Sep
public import CatalanLambda.Mirror.NVMain
public import CatalanLambda.Measure.Irrational

@[expose] public section

/-!
# Irrationality of `λ' = G/2 + 5π²/96` from `CertFacts` with `D_cert > 313/105`.
-/

open Filter

namespace CatalanLambda.Mirror

open CatalanLambda.Decay
open CatalanLambda.Measure (den_dvd_natAbs)

/-- Nonvanishing at one of the three indices, for a prime `ℓ ≡ 1 (4)`, `ℓ ≥ 13`, `ℓ ∤ q`. -/
theorem exists_h_nonvanishing (ℓ : ℕ) [Fact ℓ.Prime] (h3 : ℓ % 4 = 1) (h7 : 13 ≤ ℓ) (p q : ℤ)
    (hℓ : ¬ ℓ ∣ q.natAbs) :
    ∃ h : ℕ, (3 * ℓ - 3) / 4 ≤ h ∧ h ≤ ℓ - 1 ∧ Pbar h ((p : ℚ) / q) ≠ 0 := by
  have hr : ¬ ℓ ∣ ((p : ℚ) / q).den := fun hd => hℓ (hd.trans (den_dvd_natAbs p q))
  rcases mirror_nonvanishing ℓ h3 h7 _ hr with h | h | h
  · exact ⟨ℓ - 1, by omega, le_rfl, h⟩
  · exact ⟨ℓ - 2, by omega, by omega, h⟩
  · exact ⟨(3 * ℓ - 3) / 4, le_rfl, by omega, h⟩

/-- Primes `ℓ ≡ 3 (4)` above any bound and not dividing `q` (`q ≠ 0`). -/
theorem exists_prime_one_mod_four (N : ℕ) (q : ℤ) (hq : q ≠ 0) :
    ∃ ℓ : ℕ, N < ℓ ∧ ℓ.Prime ∧ ℓ % 4 = 1 ∧ ¬ ℓ ∣ q.natAbs := by
  obtain ⟨ℓ, hℓN, hℓp, hℓm⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := 4) (a := 1)
    (by decide) (max N q.natAbs)
  refine ⟨ℓ, lt_of_le_of_lt (le_max_left _ _) hℓN, hℓp, ?_, ?_⟩
  · have := (ZMod.natCast_eq_natCast_iff' ℓ 1 4).1 (by simpa using hℓm)
    simpa using this
  · intro hd
    have := Nat.le_of_dvd (Int.natAbs_pos.2 hq) hd
    have := lt_of_le_of_lt (le_max_right _ _) hℓN
    omega

/-- **Irrationality.**  Under `CertFacts` with `D_cert > 313/105`,
`λ' = G/2 + 5π²/96` is irrational. -/
theorem lambda_mirror_irrational {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) (hD : (313 / 105 : ℝ) < F.Dcert) :
    Irrational (catalanG / 2 + 5 * Real.pi ^ 2 / 96) := by
  rw [← lamB_eq]
  rintro ⟨r, hr⟩
  set p : ℤ := r.num
  set q : ℤ := (r.den : ℤ)
  have hq : 0 < q := Int.natCast_pos.2 r.den_pos
  have hrpq : lamB = (p : ℝ) / q := by
    rw [← hr]; simp only [p, q]; exact_mod_cast (Rat.num_div_den r).symm
  set θ : ℝ := ((F.Dcert : ℝ) - 313 / 105) / 2 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  obtain ⟨h₀, H⟩ := sep_core F hθ0 (by rw [hθ]; linarith)
  -- pick ℓ large
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.log q * 4 / θ + 8)
  obtain ⟨ℓ, hℓN, hℓp, hℓ3, hℓq⟩ := exists_prime_one_mod_four (max N (4 * h₀ + 20)) q hq.ne'
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hN1 : N < ℓ := lt_of_le_of_lt (le_max_left _ _) hℓN
  have hN2 : 4 * h₀ + 20 < ℓ := lt_of_le_of_lt (le_max_right _ _) hℓN
  obtain ⟨h, hh1, hh2, hP⟩ := exists_h_nonvanishing ℓ hℓ3 (by omega) p q hℓq
  have hh0 : h₀ ≤ h := by omega
  have hclose : |lamB - (p : ℝ) / q| ≤ Real.exp (-(F.ccert : ℝ) * h) := by
    rw [hrpq]; simp [(Real.exp_pos _).le]
  have key := H h hh0 p q hq hP hclose
  -- contradiction: θ h > log q
  have hℓR : (N : ℝ) < ℓ := by exact_mod_cast hN1
  have hh3' : 3 * ℓ - 3 ≤ 4 * h := by omega
  have hh3 : (3 * (ℓ : ℝ) - 3) ≤ 4 * h := by
    have h1 : 1 ≤ ℓ := by omega
    have : ((3 * ℓ - 3 : ℕ) : ℝ) ≤ ((4 * h : ℕ) : ℝ) := by exact_mod_cast hh3'
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this
    linarith
  have hlogq : Real.log q * 4 / θ + 8 < ℓ := by linarith
  have hlq : Real.log q * 4 < θ * (ℓ - 8) := by
    have := (div_lt_iff₀ hθ0).1 (show Real.log q * 4 / θ < ℓ - 8 by linarith)
    linarith
  have hh4 : (h : ℝ) ≥ (3 * ℓ - 4) / 4 := by linarith
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  nlinarith

end CatalanLambda.Mirror
