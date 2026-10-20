module

public import CatalanArchive.CatalanLambda.Mirror.Final

@[expose] public section

/-!
# `G + 5π²/48 = 2 λ'`: an irrationality-measure corollary

From `μ(λ') ≤ 78` (in the form `|λ' - p/q| > q^(-78)` for large `q`) we obtain
`|G + 5π²/48 - p/q| > q^(-79)` for large `q` and `p` coprime to `q`.
-/

namespace CatalanLambda.Mirror

theorem catalan_add_measure_79 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(79 : ℝ))
        < |(OAI.InternalCatalan.catalan + 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q| := by
  obtain ⟨q₁, H⟩ := lambda_mirror_measure_78_catalan
  refine ⟨max q₁ (2 ^ 77), fun p q hc hq => ?_⟩
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq77 : 2 ^ 77 ≤ q := le_trans (le_max_right _ _) hq
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq77
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  set L : ℝ := OAI.InternalCatalan.catalan / 2 + 5 * Real.pi ^ 2 / 96 with hL
  have hid : (OAI.InternalCatalan.catalan + 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q
      = 2 * (L - (p : ℝ) / (2 * q)) := by
    rw [hL]; field_simp; ring
  rcases Int.even_or_odd p with ⟨p2, hp2⟩ | hodd
  · -- `p = 2 p2`
    have hdvd : p2.natAbs ∣ p.natAbs := ⟨2, by rw [hp2]; omega⟩
    have hc2 : Nat.Coprime p2.natAbs q := Nat.Coprime.coprime_dvd_left hdvd hc
    have h1 := H p2 q hc2 hq1
    have hid2 : (OAI.InternalCatalan.catalan + 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q
        = 2 * (L - (p2 : ℝ) / q) := by
      rw [hL, hp2]; push_cast; field_simp; ring
    rw [hid2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h2 : (q : ℝ) ^ (-(79 : ℝ)) ≤ (q : ℝ) ^ (-(78 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1' (by norm_num)
    have h3 : 0 ≤ |L - (p2 : ℝ) / q| := abs_nonneg _
    linarith
  · -- `p` odd: `gcd(p, 2q) = 1`
    have hodd2 : ¬ 2 ∣ p.natAbs := by
      intro h2
      have : Even p.natAbs := even_iff_two_dvd.2 h2
      rw [Int.natAbs_even] at this
      exact (Int.not_even_iff_odd.2 hodd) this
    have hc2 : Nat.Coprime p.natAbs (2 * q) := by
      apply Nat.Coprime.mul_right _ hc
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd2).symm
    have h1 := H p (2 * q) hc2 (le_trans hq1 (by omega))
    push_cast at h1
    rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hm : ((2 : ℝ) * q) ^ (-(78 : ℝ)) = (2 : ℝ) ^ (-(78 : ℝ)) * (q : ℝ) ^ (-(78 : ℝ)) :=
      Real.mul_rpow (by norm_num) hqpos.le
    have h2q : (2 : ℝ) ^ (77 : ℕ) ≤ q := by exact_mod_cast hq77
    have h278 : (2 : ℝ) ^ (-(78 : ℝ)) = 1 / 2 ^ 78 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    have hq79 : (q : ℝ) ^ (-(79 : ℝ)) = (q : ℝ) ^ (-(78 : ℝ)) * (1 / q) := by
      rw [show (-(79 : ℝ)) = -(78 : ℝ) + (-1) by norm_num, Real.rpow_add hqpos, Real.rpow_neg_one]
      simp
    have hpos : 0 < (q : ℝ) ^ (-(78 : ℝ)) := Real.rpow_pos_of_pos hqpos _
    have hinv : 1 / (q : ℝ) ≤ 2 * (1 / 2 ^ 78) := by
      rw [div_le_iff₀ hqpos]
      have : (2 : ℝ) ^ 78 = 2 * 2 ^ 77 := by norm_num
      have h77 : (0 : ℝ) < 2 ^ 77 := by positivity
      field_simp
      nlinarith
    rw [hm, h278] at h1
    calc (q : ℝ) ^ (-(79 : ℝ)) = (q : ℝ) ^ (-(78 : ℝ)) * (1 / q) := hq79
      _ ≤ (q : ℝ) ^ (-(78 : ℝ)) * (2 * (1 / 2 ^ 78)) :=
          mul_le_mul_of_nonneg_left hinv hpos.le
      _ = 2 * (1 / 2 ^ 78 * (q : ℝ) ^ (-(78 : ℝ))) := by ring
      _ < 2 * |L - (p : ℝ) / (2 * q)| := by linarith

end CatalanLambda.Mirror
