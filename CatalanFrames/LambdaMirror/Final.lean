module

public import CatalanFrames.LambdaMirror.Content
public import CatalanFrames.LambdaMirror.Decay
public import CatalanFrames.LambdaMirror.NV
public import CatalanFrames.LambdaMirror.Const
public import CatalanCore.Measure.Statements
public import CatalanLambda.Final
public import CatalanLambda.Mirror.Prime

/-!
# Mirror final statements through the generic `CatalanCore.Measure` (WP8)

The mirror constant `G/2 + 5π²/96`: irrationality, the exponent `31682445459/409965000`, the
round exponent 78, and for `G + 5π²/48 = 2 * (mirror constant)` irrationality and exponent 79.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.LambdaMirror

theorem mirRule_hasWindow : mirRule.HasWindow := by
  intro a b ha hab
  rw [mirRule_s] at hab
  push_cast at hab
  obtain ⟨q₀, H⟩ := CatalanLambda.Mirror.exists_prime_window_sq1 a b ha hab
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨l, hp, h1, h2, h3, hbad⟩ := H q hq
  refine ⟨l, hp, ?_, h2, h3, hbad⟩
  have : (l : ZMod 4) = ((1 : ℕ) : ZMod 4) :=
    (ZMod.natCast_eq_natCast_iff' l 1 4).2 (by simpa using h1)
  have h' : (l : ZMod 4) = 1 := by simpa using this
  exact h'

theorem mirRule_hbad : ∀ q : ℕ, 0 < q → ∃ N : ℕ, ∀ l : ℕ, N < l → ¬ mirRule.Bad l q := by
  intro q hq
  refine ⟨q, fun l hl ⟨h2, _⟩ => ?_⟩
  have := Nat.le_of_dvd hq h2
  nlinarith

theorem hD_cert : HasDecay (PolyFamily.ofFrame mirFrame) (((31111 / 10000 : ℚ)) : ℝ)
    (((68726 / 10000 : ℚ)) : ℝ) :=
  hasDecay CatalanLambda.Cert.certFacts

theorem hΛ_q : HasContent (PolyFamily.ofFrame mirFrame) (((313 / 105 : ℚ)) : ℝ) := by
  have := hasContent
  push_cast
  exact this

theorem hg : (0 : ℚ) < 3 / 4 ∧ (3 / 4 : ℚ) ≤ 1 := by norm_num

theorem hNV_q :
    HasNV (PolyFamily.ofFrame mirFrame) mirRule (((3 / 4 : ℚ)) : ℝ) (((1 : ℚ)) : ℝ) := by
  have := hasNV
  push_cast
  exact this

theorem mirRule_s_pos : 0 < mirRule.s := by rw [mirRule_s]; norm_num

theorem mirFamily_measure :
    (PolyFamily.ofFrame mirFrame).MeasureLB (((31682445459 / 409965000 : ℚ)) : ℝ) :=
  Measure.measure_of_frame_le mirFrame hΛ_q hD_cert (by norm_num) (by norm_num) mirRule
    mirRule_s_pos hg hNV_q mirRule_hasWindow (by rw [mirRule_s]; norm_num [measureExp])

theorem mirror_irrational_new : Irrational (mirFrame.const) :=
  Measure.irrational_of_frame mirFrame (Λ := 313 / 105) (D := 31111 / 10000)
    (c := 68726 / 10000) (g₁ := 3 / 4) (g₂ := 1)
    (by simpa using hasContent) (by simpa using hD_cert) (by norm_num) mirRule (by simp [mirRule])
    (by norm_num) mirRule_hbad (by simpa using hasNV)

theorem coprime_conv (p : ℤ) (q : ℕ) (h : Nat.Coprime p.natAbs q) : IsCoprime p (q : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  simpa [Int.gcd] using h

/-! ### The mirror statements of `ChallengeLambda.lean` -/

theorem lambdaMirror_irrational_solution :
    Irrational ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
      + 5 * Real.pi ^ 2 / 96) := by
  rw [← const_eq]; exact mirror_irrational_new

theorem lambdaMirror_irrationalityMeasure_solution {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(((31682445459 / 409965000 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          + 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := mirFamily_measure e he
  refine ⟨q₀, fun p q hc hq => ?_⟩
  have := H p q hq (coprime_conv p q hc)
  rwa [show (PolyFamily.ofFrame mirFrame).const = _ from const_eq] at this

theorem lambdaMirror_irrationalityMeasure_78_solution :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          + 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := mirFamily_measure (1 / 2) (by norm_num)
  refine ⟨max q₀ 1, fun p q hc hq => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  have h := H p q (le_trans (le_max_left _ _) hq) (coprime_conv p q hc)
  rw [show (PolyFamily.ofFrame mirFrame).const = _ from const_eq] at h
  refine lt_of_le_of_lt ?_ h
  exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)

/-! ### `2x`: from exponent 78 to exponent 79 (generic in `x`) -/

/-- If `|x - p/q| > q^(-78)` for all large `q` (`p` coprime to `q`), then
`|2x - p/q| > q^(-79)` for all large `q`. -/
theorem double_79 (x : ℝ)
    (H78 : ∃ q₁ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₁ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) < |x - (p : ℝ) / q|) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(79 : ℝ)) < |2 * x - (p : ℝ) / q| := by
  obtain ⟨q₁, H⟩ := H78
  refine ⟨max q₁ (2 ^ 77), fun p q hc hq => ?_⟩
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq77 : 2 ^ 77 ≤ q := le_trans (le_max_right _ _) hq
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq77
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hid : 2 * x - (p : ℝ) / q = 2 * (x - (p : ℝ) / (2 * q)) := by
    field_simp
  rcases Int.even_or_odd p with ⟨p2, hp2⟩ | hodd
  · have hdvd : p2.natAbs ∣ p.natAbs := ⟨2, by rw [hp2]; omega⟩
    have hc2 : Nat.Coprime p2.natAbs q := Nat.Coprime.coprime_dvd_left hdvd hc
    have h1 := H p2 q hc2 hq1
    have hid2 : 2 * x - (p : ℝ) / q = 2 * (x - (p2 : ℝ) / q) := by
      rw [hp2]; push_cast; field_simp; ring
    rw [hid2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h2 : (q : ℝ) ^ (-(79 : ℝ)) ≤ (q : ℝ) ^ (-(78 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1' (by norm_num)
    have h3 : 0 ≤ |x - (p2 : ℝ) / q| := abs_nonneg _
    linarith
  · have hodd2 : ¬ 2 ∣ p.natAbs := by
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
      _ < 2 * |x - (p : ℝ) / (2 * q)| := by linarith

theorem catalan_add_irrational_solution :
    Irrational ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48) := by
  have h0 := lambdaMirror_irrational_solution
  generalize (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) = S at h0 ⊢
  have h := h0.ratCast_mul (q := 2) (by norm_num)
  push_cast at h
  convert h using 1
  ring

theorem catalan_add_irrationalityMeasure_79_solution :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(79 : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := double_79 _ lambdaMirror_irrationalityMeasure_78_solution
  refine ⟨q₀, fun p q hc hq => ?_⟩
  have := H p q hc hq
  generalize (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) = S at this ⊢
  convert this using 3
  ring

end CatalanFrames.LambdaMirror
