module

public import CatalanFrames.Lambda.Content
public import CatalanFrames.Lambda.Decay
public import CatalanFrames.Lambda.NV
public import CatalanFrames.Lambda.Const
public import CatalanCore.Measure.Statements
public import CatalanLambda.Final

/-!
# λ final statements through the generic `CatalanCore.Measure` (negative control A)

Inputs: legacy content/decay/NV packaged as `HasContent`, `HasDecay`, `HasNV` for
`PolyFamily.ofFrame lamFrame`, the legacy prime window `exists_prime_window_sq`, and the
verified certificate `Cert.certFacts` (`D = 31111/10000`, `c = 68726/10000`).  The exponent
`31682445459/409965000` is re-derived by `measure_of_frame` and `norm_num [measureExp]`.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.Lambda

/-- The prime window for `lamRule` from the legacy `exists_prime_window_sq`. -/
theorem lamRule_hasWindow : lamRule.HasWindow := by
  intro a b ha hab
  rw [lamRule_s] at hab
  push_cast at hab
  obtain ⟨q₀, H⟩ := CatalanLambda.Measure.exists_prime_window_sq a b ha hab
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨l, hp, h3, h1, h2, hbad⟩ := H q hq
  refine ⟨l, hp, ?_, h1, h2, hbad⟩
  have : (l : ZMod 4) = ((3 : ℕ) : ZMod 4) :=
    (ZMod.natCast_eq_natCast_iff' l 3 4).2 (by simpa using h3)
  exact this

theorem lamRule_hbad : ∀ q : ℕ, 0 < q → ∃ N : ℕ, ∀ l : ℕ, N < l → ¬ lamRule.Bad l q := by
  intro q hq
  refine ⟨q, fun l hl ⟨h2, _⟩ => ?_⟩
  have := Nat.le_of_dvd hq h2
  nlinarith

theorem hD_cert : HasDecay (PolyFamily.ofFrame lamFrame) (((31111 / 10000 : ℚ)) : ℝ)
    (((68726 / 10000 : ℚ)) : ℝ) :=
  hasDecay CatalanLambda.Cert.certFacts

theorem hΛ_q : HasContent (PolyFamily.ofFrame lamFrame) (((313 / 105 : ℚ)) : ℝ) := by
  have := hasContent
  push_cast
  exact this

theorem hg : (0 : ℚ) < 3 / 4 ∧ (3 / 4 : ℚ) ≤ 1 := by norm_num

theorem hNV_q : HasNV (PolyFamily.ofFrame lamFrame) lamRule (((3 / 4 : ℚ)) : ℝ) (((1 : ℚ)) : ℝ) := by
  have := hasNV
  push_cast
  exact this

theorem lamRule_s_pos : 0 < lamRule.s := by rw [lamRule_s]; norm_num

/-- **Negative control A.**  The exponent `31682445459/409965000 ≈ 77.28` via the generic theorem. -/
theorem lamFamily_measure :
    (PolyFamily.ofFrame lamFrame).MeasureLB (((31682445459 / 409965000 : ℚ)) : ℝ) :=
  Measure.measure_of_frame_le lamFrame hΛ_q hD_cert (by norm_num) (by norm_num) lamRule
    lamRule_s_pos hg hNV_q lamRule_hasWindow (by rw [lamRule_s]; norm_num [measureExp])

theorem lambda_irrational_new : Irrational (lamFrame.const) :=
  Measure.irrational_of_frame lamFrame (Λ := 313 / 105) (D := 31111 / 10000)
    (c := 68726 / 10000) (g₁ := 3 / 4) (g₂ := 1)
    (by simpa using hasContent) (by simpa using hD_cert) (by norm_num) lamRule (by simp [lamRule])
    (by norm_num) lamRule_hbad (by simpa using hasNV)

/-! ### The statements of `SolutionLambda.lean` -/

theorem coprime_conv (p : ℤ) (q : ℕ) (h : Nat.Coprime p.natAbs q) : IsCoprime p (q : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  simpa [Int.gcd] using h

theorem lambda_irrational_solution :
    Irrational ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
      - 5 * Real.pi ^ 2 / 96) := by
  rw [← const_eq]; exact lambda_irrational_new

theorem lambda_irrationalityMeasure_solution {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(((31682445459 / 409965000 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          - 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := lamFamily_measure e he
  refine ⟨q₀, fun p q hc hq => ?_⟩
  have := H p q hq (coprime_conv p q hc)
  rwa [show (PolyFamily.ofFrame lamFrame).const = _ from const_eq] at this

theorem lambda_irrationalityMeasure_78_solution :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          - 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := lamFamily_measure (1 / 2) (by norm_num)
  refine ⟨max q₀ 1, fun p q hc hq => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  have h := H p q (le_trans (le_max_left _ _) hq) (coprime_conv p q hc)
  rw [show (PolyFamily.ofFrame lamFrame).const = _ from const_eq] at h
  refine lt_of_le_of_lt ?_ h
  exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)

end CatalanFrames.Lambda
