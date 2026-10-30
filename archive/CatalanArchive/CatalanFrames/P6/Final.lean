module

public import CatalanFrames.P6.Instance
public import CatalanCore.Measure.Scaling

/-!
# L(2, χ₋₃): final statements (WP12)

`p6Frame.const = chi3L2 / 4`, so `chi3L2 = 4 * const + 0` and the measure bound transfers by
`MeasureLBAt.affine` (same exponent).  Everything depends on the decay row only through
`P6.p6Exp` (see `Instance.lean`); the round exponent `31` is a one-line change if the row changes.
-/

@[expose] public section

open CatalanCore CatalanCore.Measure

namespace CatalanFrames.P6

theorem chi3L2_eq : chi3L2 = ((4 : ℚ) : ℝ) * p6Frame.const + ((0 : ℚ) : ℝ) := by
  rw [p6Frame_const]; push_cast; ring

theorem chi3_irrational : Irrational chi3L2 := by
  rw [chi3L2_eq]; exact irrational_affine p6_irrational 4 0 (by norm_num)

theorem p6Exp_nonneg : (0 : ℝ) ≤ (p6Exp : ℝ) := by
  have : (0 : ℚ) ≤ p6Exp := by norm_num [p6Exp, measureExp, decC, decD, contLam, rule_s]
  exact_mod_cast this

/-- MeasureLBAt for `chi3L2` at the exact exponent. -/
theorem chi3_measureLBAt : MeasureLBAt chi3L2 (p6Exp : ℝ) := by
  rw [chi3L2_eq]
  exact MeasureLBAt.affine p6Exp_nonneg p6_measure 4 0 (by norm_num)

/-- **Exact exponent.** -/
theorem chi3_irrationalityMeasure {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-((p6Exp : ℝ) + e)) < |chi3L2 - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := chi3_measureLBAt e he
  exact ⟨q₀, fun p q hc hq => H p q hq ((isCoprime_iff_natCoprime p q).2 hc)⟩

/-- the exact exponent is `224384787/7474000 ≈ 30.022` (row D). -/
theorem p6Exp_eq : p6Exp = 224384787 / 7474000 := by
  norm_num [p6Exp, measureExp, decC, decD, contLam, rule_s]

theorem chi3_lt_31 : (p6Exp : ℝ) < 31 := by
  have : p6Exp < 31 := by rw [p6Exp_eq]; norm_num
  exact_mod_cast this

/-- **Round exponent 31.**  (Row D swap done: was 37 for row A.) -/
theorem chi3_irrationalityMeasure_31 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(31 : ℝ)) < |chi3L2 - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := chi3_measureLBAt.round chi3_lt_31
  refine ⟨q₀, fun p q hc hq => ?_⟩
  have := H p q hq ((isCoprime_iff_natCoprime p q).2 hc)
  simpa [chi3L2_eq] using this

end CatalanFrames.P6
