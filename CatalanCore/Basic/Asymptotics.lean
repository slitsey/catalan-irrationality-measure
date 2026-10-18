module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

/-!
# Elementary asymptotics used by the content engine

* `ev_log_le`, `ev_log_sq_le` : `log x ≤ δ x`, `(log x)² ≤ δ x` eventually;
* `sum_max_le`   : the sum of a pointwise `max` of an increasing and a decreasing line
  (the source of `I(c) = 1/(2(1+c)) + c/2`);
* `ev_sqrt_log_small` : `(⌊√(L h)⌋+1)(log₂(L h)+1) log(L h) ≤ δ h` eventually.
-/

open Finset Filter Topology

namespace CatalanCore.Basic

lemma ev_log_le {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop, Real.log x ≤ δ * x := by
  have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).eventually
    (gt_mem_nhds hδ)
  filter_upwards [this, eventually_gt_atTop 0] with x hx hx0
  simp only [pow_one, one_mul, add_zero] at hx
  rw [div_lt_iff₀ hx0] at hx
  linarith

lemma ev_log_sq_le {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ δ * x := by
  have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).eventually
    (gt_mem_nhds hδ)
  filter_upwards [this, eventually_gt_atTop 0] with x hx hx0
  simp only [one_mul, add_zero] at hx
  rw [div_lt_iff₀ hx0] at hx
  linarith

lemma sum_range_cast (m : ℕ) : ∑ a ∈ Finset.range m, (a : ℝ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The sum of a pointwise-`max` of an increasing and a decreasing line. -/
lemma sum_max_le (c d : ℝ) (hc : 0 < c) (hd : 0 ≤ d) (h : ℕ) (T : ℕ → ℝ)
    (hT : ∀ a < h, T a ≤ max (c * a + d) ((h : ℝ) - a)) :
    ∑ a ∈ Finset.range h, T a ≤
      ((h : ℝ) + (1 + c) / 2 - d) ^ 2 / (2 * (1 + c)) + c * h * (h - 1) / 2 + d * h := by
  have hs : 0 < 1 + c := by linarith
  set m : ℕ := ⌈((h : ℝ) - d) / (1 + c)⌉₊ with hm
  have hmh : m ≤ h := by
    rw [hm, Nat.ceil_le]
    rw [div_le_iff₀ hs]
    have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    nlinarith
  have h1 : ∀ a < m, (c * a + d) ≤ (h : ℝ) - a := by
    intro a ha
    have : (a : ℝ) < ((h : ℝ) - d) / (1 + c) := Nat.lt_ceil.mp ha
    rw [lt_div_iff₀ hs] at this
    nlinarith
  have h2 : ∀ a, m ≤ a → (h : ℝ) - a ≤ c * a + d := by
    intro a ha
    have : ((h : ℝ) - d) / (1 + c) ≤ a := (Nat.le_ceil _).trans (by exact_mod_cast ha)
    rw [div_le_iff₀ hs] at this
    nlinarith
  have hsplit := Finset.sum_range_add_sum_Ico T hmh
  have hA : ∑ a ∈ Finset.range m, T a ≤ ∑ a ∈ Finset.range m, ((h : ℝ) - a) := by
    apply Finset.sum_le_sum
    intro a ha
    have ha' := Finset.mem_range.mp ha
    refine (hT a (by omega)).trans (max_le (h1 a ha') le_rfl)
  have hB : ∑ a ∈ Finset.Ico m h, T a ≤ ∑ a ∈ Finset.Ico m h, (c * a + d) := by
    apply Finset.sum_le_sum
    intro a ha
    have ha' := Finset.mem_Ico.mp ha
    refine (hT a ha'.2).trans (max_le le_rfl (h2 a ha'.1))
  have hC : ∑ a ∈ Finset.Ico m h, (c * (a : ℝ) + d) =
      ∑ a ∈ Finset.range h, (c * (a : ℝ) + d) - ∑ a ∈ Finset.range m, (c * (a : ℝ) + d) :=
    Finset.sum_Ico_eq_sub _ hmh
  have e1 : ∑ a ∈ Finset.range m, ((h : ℝ) - a) = m * h - m * (m - 1) / 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sum_range_cast, nsmul_eq_mul]
  have e2 : ∀ n : ℕ, ∑ a ∈ Finset.range n, (c * (a : ℝ) + d) = c * (n * (n - 1) / 2) + n * d := by
    intro n
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_cast, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  rw [hC, e2, e2] at hB
  rw [e1] at hA
  have hq : ((h : ℝ) + (1 + c) / 2 - d) ^ 2 / (2 * (1 + c)) + c * h * (h - 1) / 2 + d * h
      - ((m * h - m * (m - 1) / 2) + (c * (h * (h - 1) / 2) + h * d - (c * (m * (m - 1) / 2) + m * d)))
      = (((1 + c) * m - ((h : ℝ) + (1 + c) / 2 - d)) ^ 2) / (2 * (1 + c)) := by
    field_simp
    ring
  have hnn : 0 ≤ (((1 + c) * m - ((h : ℝ) + (1 + c) / 2 - d)) ^ 2) / (2 * (1 + c)) := by positivity
  linarith

/-- The number of prime powers `≤ L h` which are not primes is `O(√h log h)`, hence `o(h)`
even after multiplying by `log (L h)`. -/
lemma ev_sqrt_log_small {L : ℕ} (hL : 1 ≤ L) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ h : ℕ in atTop,
      ((Nat.sqrt (L * h) : ℝ) + 1) * ((Nat.log 2 (L * h) : ℝ) + 1) * Real.log (L * h : ℝ)
        ≤ δ * h := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have tc : Tendsto (fun h : ℕ => (h : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ty : Tendsto (fun h : ℕ => Real.sqrt ((L : ℝ) * (h : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tc.const_mul_atTop (by linarith))
  have hδ' : 0 < δ / (20 * L) := by positivity
  have evC : ∀ᶠ h : ℕ in atTop, (Real.log (Real.sqrt ((L : ℝ) * (h : ℝ))) ^ 2 ≤
      (δ / (20 * L)) * Real.sqrt ((L : ℝ) * (h : ℝ)) ∧
      1 ≤ Real.log (Real.sqrt ((L : ℝ) * (h : ℝ)))) ∧ 1 ≤ Real.sqrt ((L : ℝ) * (h : ℝ)) :=
    ty.eventually (((ev_log_sq_le hδ').and
      (Real.tendsto_log_atTop.eventually_ge_atTop 1)).and (eventually_ge_atTop 1))
  filter_upwards [evC, eventually_ge_atTop 1] with h ⟨⟨hC1, hC2⟩, hC3⟩ h1
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast h1
  set y := Real.sqrt ((L : ℝ) * (h : ℝ)) with hy
  have hy2 : y ^ 2 = L * h := Real.sq_sqrt (by positivity)
  have hcast : ((L * h : ℕ) : ℝ) = (L : ℝ) * h := by push_cast; ring
  have hN : (Nat.sqrt (L * h) : ℝ) ≤ y := by
    have := Real.nat_sqrt_le_real_sqrt (a := L * h)
    rw [hcast] at this
    exact this
  have hlx : Real.log ((L : ℝ) * h) = 2 * Real.log y := by
    rw [← hy2, Real.log_pow]; norm_num
  have hE : (Nat.log 2 (L * h) : ℝ) ≤ 4 * Real.log y := by
    have h1' := Real.natLog_le_logb (L * h) 2
    rw [hcast] at h1'; push_cast at h1'
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hlx0 : 0 ≤ Real.log ((L : ℝ) * h) := Real.log_nonneg (by nlinarith)
    have : Real.logb 2 ((L : ℝ) * h) ≤ 2 * Real.log ((L : ℝ) * h) := by
      unfold Real.logb
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have h3 : ((Nat.sqrt (L * h) : ℝ) + 1) ≤ 2 * y := by linarith
  have h4 : ((Nat.log 2 (L * h) : ℝ) + 1) ≤ 5 * Real.log y := by linarith
  rw [hlx]
  calc _ ≤ (2 * y) * (5 * Real.log y) * (2 * Real.log y) := by
        apply mul_le_mul (mul_le_mul h3 h4 (by positivity) (by positivity)) le_rfl
          (by linarith) (by positivity)
    _ = 20 * y * Real.log y ^ 2 := by ring
    _ ≤ 20 * y * ((δ / (20 * L)) * y) := by
        apply mul_le_mul_of_nonneg_left hC1 (by positivity)
    _ = δ * (y ^ 2 / L) := by field_simp
    _ = δ * h := by rw [hy2]; field_simp

end CatalanCore.Basic
