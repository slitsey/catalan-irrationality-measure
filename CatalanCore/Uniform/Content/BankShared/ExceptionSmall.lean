import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
set_option Elab.async false

/-! # Shared contract 3 (lane H17): a fixed exceptional set costs `o(r^2)`

`fixed_exception_price_small`: for a fixed finite set `F` of primes (or any naturals) and prices
`e r p ≤ C r (log (r+1) + 1)` on `F`, the weighted sum `∑_{p ∈ F} e r p * log p` is eventually at
most `ε r^2`, for every `ε > 0`.

`Ecrude c r p = 2 r (3 ⌊log_p (14 r)⌋ + c)` is the crude exponent that clears every coefficient of
every member for frames with two-term denominators (SPEC, "Complete treatment of small and
exceptional primes"); `Ecrude_le` shows it satisfies the hypothesis with `C = 48 + 2 c`, and
`fixed_exception_E_crude_small` is the resulting total cost for the fixed exceptional set. -/

namespace CatalanCore.Uniform.Content.BankShared
open Filter

/-- `K (log (r+1) + 1) ≤ ε r` eventually. -/
theorem log_budget_eventually (K ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, K * (Real.log ((r : ℝ) + 1) + 1) ≤ ε * (r : ℝ) := by
  set K' : ℝ := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set δ : ℝ := ε / (2 * (K' + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hlo := Real.isLittleO_log_id_atTop.def hδ0
  have hlo' : ∀ᶠ r : ℕ in atTop, ‖Real.log (r : ℝ)‖ ≤ δ * ‖(r : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually hlo
  obtain ⟨R1, hR1⟩ := eventually_atTop.1 hlo'
  refine eventually_atTop.2 ⟨max (max R1 1) ⌈4 * K' / ε⌉₊, fun r hr => ?_⟩
  have hr1 : R1 ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
  have hr2 : 1 ≤ r := (le_max_right _ _).trans ((le_max_left _ _).trans hr)
  have hr3 : ⌈4 * K' / ε⌉₊ ≤ r := (le_max_right _ _).trans hr
  have hx1 : (1 : ℝ) ≤ r := by exact_mod_cast hr2
  have hx0 : (0 : ℝ) < r := by linarith
  have hlogr := hR1 r hr1
  rw [Real.norm_of_nonneg (Real.log_nonneg hx1), Real.norm_of_nonneg hx0.le] at hlogr
  have hl2 : Real.log ((r : ℝ) + 1) ≤ 1 + Real.log r := by
    have : Real.log ((r : ℝ) + 1) ≤ Real.log (2 * r) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hx0.ne'] at this
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hKr : 4 * K' / ε ≤ r := (Nat.ceil_le).1 hr3
  have hKr' : 4 * K' ≤ ε * r := by
    have := (div_le_iff₀ hε).1 hKr; linarith
  have hKle : K * (Real.log ((r : ℝ) + 1) + 1) ≤ K' * (Real.log ((r : ℝ) + 1) + 1) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ (r : ℝ) + 1); linarith)
  have hδK : K' * δ * r ≤ ε * r / 2 := by
    have : K' * δ ≤ ε / 2 := by
      rw [hδ]
      have hden : 0 < 2 * (K' + 1) := by positivity
      rw [mul_div_assoc', div_le_div_iff₀ hden (by norm_num)]
      nlinarith
    nlinarith
  calc K * (Real.log ((r : ℝ) + 1) + 1) ≤ K' * (Real.log ((r : ℝ) + 1) + 1) := hKle
    _ ≤ K' * (2 + δ * r) := by
        apply mul_le_mul_of_nonneg_left _ hK'0
        linarith
    _ = 2 * K' + K' * δ * r := by ring
    _ ≤ ε * r := by nlinarith

/-- **Shared contract 3.**  A fixed finite exceptional set of primes with prices
`≤ C r (log (r+1) + 1)` costs `o(r^2)` in total. -/
theorem fixed_exception_price_small (F : Finset ℕ) (C : ℝ) (e : ℕ → ℕ → ℝ)
    (he : ∀ r : ℕ, ∀ p ∈ F, e r p ≤ C * r * (Real.log ((r : ℝ) + 1) + 1)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop,
      ∑ p ∈ F, e r p * Real.log p ≤ ε * (r : ℝ) ^ 2 := by
  intro ε hε
  set Λ : ℝ := ∑ p ∈ F, Real.log p with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  filter_upwards [log_budget_eventually (C' * Λ) ε hε] with r hr
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hL1 : 0 ≤ Real.log ((r : ℝ) + 1) + 1 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ (r : ℝ) + 1); linarith
  have hterm : ∀ p ∈ F, e r p * Real.log p ≤ C' * r * (Real.log ((r : ℝ) + 1) + 1) * Real.log p := by
    intro p hp
    have hlp := Real.log_natCast_nonneg p
    refine mul_le_mul_of_nonneg_right ((he r p hp).trans ?_) hlp
    have : C * r ≤ C' * r := mul_le_mul_of_nonneg_right (le_max_left _ _) hr0
    exact mul_le_mul_of_nonneg_right this hL1
  calc ∑ p ∈ F, e r p * Real.log p
      ≤ ∑ p ∈ F, C' * r * (Real.log ((r : ℝ) + 1) + 1) * Real.log p := Finset.sum_le_sum hterm
    _ = r * (C' * Λ * (Real.log ((r : ℝ) + 1) + 1)) := by
        rw [← Finset.mul_sum, ← hΛ]
        ring
    _ ≤ r * (ε * r) := mul_le_mul_of_nonneg_left hr hr0
    _ = ε * (r : ℝ) ^ 2 := by ring

/-- The crude exponent `2 r (3 ⌊log_p (14 r)⌋ + c)`. -/
def Ecrude (c r p : ℕ) : ℕ := 2 * r * (3 * Nat.log p (14 * r) + c)

theorem Ecrude_le (c : ℕ) {p : ℕ} (hp : 2 ≤ p) (r : ℕ) :
    (Ecrude c r p : ℝ) ≤ (48 + 2 * c) * r * (Real.log ((r : ℝ) + 1) + 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [Ecrude]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 : (0 : ℝ) < r := by linarith
  set L := Nat.log p (14 * r) with hL
  have hpow : p ^ L ≤ 14 * r := Nat.pow_log_le_self p (by omega)
  have hlogp : (1 : ℝ) / 2 ≤ Real.log p := by
    have h2 : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp)
    have := Real.log_two_gt_d9; linarith
  have hLlog : (L : ℝ) * Real.log p ≤ Real.log (14 * r) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  have hlog14 : Real.log 14 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    have : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 3
    nlinarith
  have hlogr : Real.log r ≤ Real.log ((r : ℝ) + 1) := Real.log_le_log hx0 (by linarith)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hLb : (L : ℝ) ≤ 2 * (3 + Real.log ((r : ℝ) + 1)) := by
    have h14r : Real.log (14 * r) = Real.log 14 + Real.log r :=
      Real.log_mul (by norm_num) hx0.ne'
    have : (L : ℝ) * (1 / 2) ≤ (L : ℝ) * Real.log p := mul_le_mul_of_nonneg_left hlogp hL0
    nlinarith
  have hlp0 : 0 ≤ Real.log ((r : ℝ) + 1) := Real.log_nonneg (by linarith)
  unfold Ecrude
  push_cast
  rw [← hL]
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  nlinarith [mul_nonneg hx0.le hlp0, mul_nonneg hx0.le hc0, mul_nonneg hx0.le (mul_nonneg hx0.le hc0)]

/-- **Total cost of the fixed exceptional set at the crude exponent.** -/
theorem fixed_exception_E_crude_small (F : Finset ℕ) (hF : ∀ p ∈ F, 2 ≤ p) (c : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop,
      ∑ p ∈ F, (Ecrude c r p : ℝ) * Real.log p ≤ ε * (r : ℝ) ^ 2 :=
  fixed_exception_price_small F (48 + 2 * c) (fun r p => (Ecrude c r p : ℝ))
    (fun r p hp => Ecrude_le c (hF p hp) r)

end CatalanCore.Uniform.Content.BankShared
