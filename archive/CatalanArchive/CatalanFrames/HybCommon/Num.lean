module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# The arithmetic of the clean-up of the `m`-dependent and `log r` terms (seven deficits)

Constant `Λ₁ = 24729491161/6665218560 - 1/448 - 1/576 - 1/352`.  Frame independent; shared by λ and the mirror.
-/

open Filter

namespace CatalanFrames.HybCommon

theorem eventually_log_le {e : ℝ} (he : 0 < e) :
    ∀ᶠ r : ℕ in atTop, Real.log r ≤ e * r := by
  have h := Real.isLittleO_log_id_atTop.bound he
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with r hr
  simp only [id, Real.norm_eq_abs] at hr
  exact (le_abs_self _).trans (hr.trans (by rw [abs_of_nonneg (Nat.cast_nonneg r)]))

/-- The arithmetic of the clean-up for the four deficits E (both classes), B, C5. -/
theorem num5 {Λ ε r L m lg : ℝ} (hΛ : 24729491161 / 6665218560 ≤ Λ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 100) (hr : 3 ≤ ε * r) (hL0 : 0 ≤ L) (hL : L ≤ ε / 10 * r)
    (hm : r / 8 - 1 ≤ m)
    (hmain : lg ≤ (24994314577 / 6665218560 + ε / 10) * r ^ 2
      - m * ((1 / 7 - ε / 10) * r - 4 * L) - m * ((7 / 80 - ε / 10) * r - 6 * L)
      - (1 / 128 - ε / 10) * r ^ 2 - (1 / 320 - ε / 10) * r ^ 2) :
    lg ≤ (Λ + ε) * r ^ 2 := by
  have hr0 : 0 ≤ r := by
    by_contra h
    push Not at h
    nlinarith
  have hX1 : 0 ≤ (1 / 7 - ε / 10) * r - 4 * L := by nlinarith
  have hX2 : 0 ≤ (7 / 80 - ε / 10) * r - 6 * L := by nlinarith
  have h1 : (r / 8 - 1) * ((1 / 7 - ε / 10) * r - 4 * L) ≤ m * ((1 / 7 - ε / 10) * r - 4 * L) :=
    mul_le_mul_of_nonneg_right hm hX1
  have h2 : (r / 8 - 1) * ((7 / 80 - ε / 10) * r - 6 * L) ≤
      m * ((7 / 80 - ε / 10) * r - 6 * L) :=
    mul_le_mul_of_nonneg_right hm hX2
  have hrL : r * L ≤ ε / 10 * r ^ 2 := by nlinarith
  have hrr : 0 ≤ r ^ 2 := sq_nonneg r
  have hlin : 129 / 560 * r ≤ ε / 10 * r ^ 2 := by nlinarith
  nlinarith

/-- The arithmetic of the clean-up for the seven deficits (E, B, C5, C7, GK). -/
theorem num7 {Λ ε r L m lg : ℝ}
    (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 100) (hr : 3 ≤ ε * r) (hL0 : 0 ≤ L) (hL : L ≤ ε / 10 * r)
    (hm : r / 8 - 1 ≤ m)
    (hmain : lg ≤ (24994314577 / 6665218560 + ε / 10) * r ^ 2
      - m * ((1 / 7 - ε / 10) * r - 4 * L) - m * ((7 / 80 - ε / 10) * r - 6 * L)
      - (1 / 128 - ε / 10) * r ^ 2 - (1 / 320 - ε / 10) * r ^ 2 - (1 / 448 - ε / 10) * r ^ 2
      - m * ((1 / 72 - ε / 10) * r - 2 * L) - m * ((1 / 44 - ε / 10) * r - 2 * L)) :
    lg ≤ (Λ + ε) * r ^ 2 := by
  have hr0 : 0 ≤ r := by
    by_contra h
    push Not at h
    nlinarith
  have hX1 : 0 ≤ (1 / 7 - ε / 10) * r - 4 * L := by nlinarith
  have hX2 : 0 ≤ (7 / 80 - ε / 10) * r - 6 * L := by nlinarith
  have hX3 : 0 ≤ (1 / 72 - ε / 10) * r - 2 * L := by nlinarith
  have hX4 : 0 ≤ (1 / 44 - ε / 10) * r - 2 * L := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hm hX1
  have h2 := mul_le_mul_of_nonneg_right hm hX2
  have h3 := mul_le_mul_of_nonneg_right hm hX3
  have h4 := mul_le_mul_of_nonneg_right hm hX4
  have hrL : r * L ≤ ε / 10 * r ^ 2 := by nlinarith
  have hrr : 0 ≤ r ^ 2 := sq_nonneg r
  have hlin : r ≤ ε / 3 * r ^ 2 := by nlinarith
  nlinarith

end CatalanFrames.HybCommon
