module

public import CatalanCore.Zeta5.Sum.PrimeSums
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section

/-!
# Weighted prime sums with a sublinear error, and the small-prime cost

Generic number theory used by the Lai content assembly (row LC23 and the generic part of LC22).

* `primeWin α β n` : the primes `p` with `α n < p ≤ β n`.
* `weighted_prime_sum_approx_le`, `_ge`, `weighted_prime_sum_approx` (Lai Lemma 5.1 in the form the
  content assembly consumes): if `w n p = n F(p/n) + O(E n)` for the primes of the window with
  `E n / n → 0` and `F` piecewise continuous on `[c₀, c_N]`, `0 < c₀`, then
  `n⁻² Σ_{p ∈ window} w n p log p → ∫_{c₀}^{c_N} F`; the two one-sided forms hold with one-sided
  hypotheses (the `∀ ε > 0, ∀ᶠ n` form).
* `small_primes_cost` : if the per-prime cost of `p ≤ δ n` is at most `12 n ⌊log_p (8n)⌋` then
  `Σ_{p ≤ δ n} cost(n,p) log p ≤ (12 δ + ε) n²` eventually (Lai (5.6)-(5.7)).
-/

set_option linter.deprecated false

open Filter Finset Set MeasureTheory
open scoped Topology

namespace CatalanCore.NT.WeightedPrimeSum

open CatalanCore.Zeta5.Sum OAI.Zeta5.Workers.W14

/-- The primes `p` with `α n < p ≤ β n`. -/
noncomputable def primeWin (α β : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Ioc ⌊α * n⌋₊ ⌊β * n⌋₊).filter Nat.Prime

theorem mem_primeWin {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) {n p : ℕ} :
    p ∈ primeWin α β n ↔ α * n < (p : ℝ) ∧ (p : ℝ) ≤ β * n ∧ p.Prime :=
  mem_primeInterval_iff (mul_nonneg hα n.cast_nonneg)
    (mul_le_mul_of_nonneg_right hαβ n.cast_nonneg) p

theorem prime_of_mem_primeWin {α β : ℝ} {n p : ℕ} (h : p ∈ primeWin α β n) : p.Prime :=
  (Finset.mem_filter.1 h).2

theorem log_nonneg_of_prime {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by exact_mod_cast hp.one_lt.le)

/-- Chebyshev: the total log-mass of the window is at most `log 4 · β · n`. -/
theorem sum_log_primeWin_le {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (n : ℕ) :
    ∑ p ∈ primeWin α β n, Real.log (p : ℝ) ≤ Real.log 4 * β * n := by
  have h1 : ∑ p ∈ primeWin α β n, Real.log (p : ℝ) = primeIntervalSum (α * n) (β * n) := rfl
  rw [h1, primeIntervalSum_eq_theta_sub (mul_le_mul_of_nonneg_right hαβ n.cast_nonneg)]
  have h2 := Chebyshev.theta_nonneg (α * n)
  have h3 := theta_le_linear (y := β * n) (mul_nonneg (hα.trans hαβ) n.cast_nonneg)
  linarith

/-- The normalised Riemann sum over the window, in the natural-number form. -/
theorem weighted_prime_sum_tendsto_win {F : ℝ → ℝ} {c : ℕ → ℝ} {N : ℕ} (h0 : 0 < c 0)
    (hF : PiecewiseCont F c N) :
    Tendsto (fun n : ℕ => (∑ p ∈ primeWin (c 0) (c N) n, F ((p : ℝ) / n) * Real.log (p : ℝ)) / n)
      atTop (𝓝 (∫ x in c 0..c N, F x)) :=
  weighted_prime_sum_tendsto_nat h0 hF

private theorem win_le {F : ℝ → ℝ} {c : ℕ → ℝ} {N : ℕ} (hF : PiecewiseCont F c N) :
    c 0 ≤ c N := c_mono hF.1 N le_rfl

/-- One-sided (upper) form of Lai Lemma 5.1 with a sublinear error. -/
theorem weighted_prime_sum_approx_le {F : ℝ → ℝ} {c : ℕ → ℝ} {N : ℕ} (h0 : 0 < c 0)
    (hF : PiecewiseCont F c N) (w : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (hE0 : ∀ n, 0 ≤ E n)
    (hE : Tendsto (fun n : ℕ => E n / n) atTop (𝓝 0))
    (hw : ∀ n p, p ∈ primeWin (c 0) (c N) n → w n p ≤ n * F ((p : ℝ) / n) + E n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (∑ p ∈ primeWin (c 0) (c N) n, w n p * Real.log (p : ℝ)) / (n : ℝ) ^ 2 ≤
        (∫ x in c 0..c N, F x) + ε := by
  have hα : 0 ≤ c 0 := h0.le
  have hαβ := win_le hF
  have hT := weighted_prime_sum_tendsto_win h0 hF
  have e1 := hT.eventually (gt_mem_nhds (show (∫ x in c 0..c N, F x) <
    (∫ x in c 0..c N, F x) + ε / 2 by linarith))
  have hE' : Tendsto (fun n : ℕ => Real.log 4 * c N * (E n / n)) atTop (𝓝 0) := by
    simpa using hE.const_mul (Real.log 4 * c N)
  have e2 := hE'.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [e1, e2, eventually_ge_atTop 1] with n h1 h2 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set T := ∑ p ∈ primeWin (c 0) (c N) n, F ((p : ℝ) / n) * Real.log (p : ℝ) with hTdef
  have hS : ∑ p ∈ primeWin (c 0) (c N) n, w n p * Real.log (p : ℝ) ≤
      n * T + E n * (Real.log 4 * c N * n) := by
    calc ∑ p ∈ primeWin (c 0) (c N) n, w n p * Real.log (p : ℝ)
        ≤ ∑ p ∈ primeWin (c 0) (c N) n,
            ((n : ℝ) * (F ((p : ℝ) / n) * Real.log (p : ℝ)) + E n * Real.log (p : ℝ)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have := mul_le_mul_of_nonneg_right (hw n p hp)
            (log_nonneg_of_prime (prime_of_mem_primeWin hp))
          linarith
      _ = n * T + E n * ∑ p ∈ primeWin (c 0) (c N) n, Real.log (p : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ n * T + E n * (Real.log 4 * c N * n) := by
          have := sum_log_primeWin_le hα hαβ n
          have := mul_le_mul_of_nonneg_left this (hE0 n)
          linarith
  have hdiv : (n * T + E n * (Real.log 4 * c N * n)) / (n : ℝ) ^ 2 =
      T / n + Real.log 4 * c N * (E n / n) := by
    field_simp
  rw [div_le_iff₀ (by positivity)]
  have h3 : (n * T + E n * (Real.log 4 * c N * n)) ≤
      ((∫ x in c 0..c N, F x) + ε) * (n : ℝ) ^ 2 := by
    rw [← div_le_iff₀ (by positivity), hdiv]
    linarith
  linarith

/-- One-sided (lower) form of Lai Lemma 5.1 with a sublinear error. -/
theorem weighted_prime_sum_approx_ge {F : ℝ → ℝ} {c : ℕ → ℝ} {N : ℕ} (h0 : 0 < c 0)
    (hF : PiecewiseCont F c N) (w : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (hE0 : ∀ n, 0 ≤ E n)
    (hE : Tendsto (fun n : ℕ => E n / n) atTop (𝓝 0))
    (hw : ∀ n p, p ∈ primeWin (c 0) (c N) n → n * F ((p : ℝ) / n) - E n ≤ w n p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (∫ x in c 0..c N, F x) - ε ≤
        (∑ p ∈ primeWin (c 0) (c N) n, w n p * Real.log (p : ℝ)) / (n : ℝ) ^ 2 := by
  have hα : 0 ≤ c 0 := h0.le
  have hαβ := win_le hF
  have hT := weighted_prime_sum_tendsto_win h0 hF
  have e1 := hT.eventually (lt_mem_nhds (show (∫ x in c 0..c N, F x) - ε / 2 <
    (∫ x in c 0..c N, F x) by linarith))
  have hE' : Tendsto (fun n : ℕ => Real.log 4 * c N * (E n / n)) atTop (𝓝 0) := by
    simpa using hE.const_mul (Real.log 4 * c N)
  have e2 := hE'.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [e1, e2, eventually_ge_atTop 1] with n h1 h2 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set T := ∑ p ∈ primeWin (c 0) (c N) n, F ((p : ℝ) / n) * Real.log (p : ℝ) with hTdef
  have hS : n * T - E n * (Real.log 4 * c N * n) ≤
      ∑ p ∈ primeWin (c 0) (c N) n, w n p * Real.log (p : ℝ) := by
    calc n * T - E n * (Real.log 4 * c N * n)
        ≤ n * T - E n * ∑ p ∈ primeWin (c 0) (c N) n, Real.log (p : ℝ) := by
          have := sum_log_primeWin_le hα hαβ n
          have := mul_le_mul_of_nonneg_left this (hE0 n)
          linarith
      _ = ∑ p ∈ primeWin (c 0) (c N) n,
            ((n : ℝ) * (F ((p : ℝ) / n) * Real.log (p : ℝ)) - E n * Real.log (p : ℝ)) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ ∑ p ∈ primeWin (c 0) (c N) n, w n p * Real.log (p : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have := mul_le_mul_of_nonneg_right (hw n p hp)
            (log_nonneg_of_prime (prime_of_mem_primeWin hp))
          linarith
  have hdiv : (n * T - E n * (Real.log 4 * c N * n)) / (n : ℝ) ^ 2 =
      T / n - Real.log 4 * c N * (E n / n) := by
    field_simp
  rw [le_div_iff₀ (by positivity)]
  have h3 : ((∫ x in c 0..c N, F x) - ε) * (n : ℝ) ^ 2 ≤
      (n * T - E n * (Real.log 4 * c N * n)) := by
    rw [← le_div_iff₀ (by positivity), hdiv]
    linarith
  linarith

/-- Lai Lemma 5.1 with a sublinear two-sided error. -/
theorem weighted_prime_sum_approx {F : ℝ → ℝ} {c : ℕ → ℝ} {N : ℕ} (h0 : 0 < c 0)
    (hF : PiecewiseCont F c N) (w : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (hE0 : ∀ n, 0 ≤ E n)
    (hE : Tendsto (fun n : ℕ => E n / n) atTop (𝓝 0))
    (hw : ∀ n p, p ∈ primeWin (c 0) (c N) n → |w n p - n * F ((p : ℝ) / n)| ≤ E n) :
    Tendsto (fun n : ℕ =>
      (∑ p ∈ primeWin (c 0) (c N) n, w n p * Real.log (p : ℝ)) / (n : ℝ) ^ 2)
      atTop (𝓝 (∫ x in c 0..c N, F x)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have := weighted_prime_sum_approx_ge h0 hF w E hE0 hE
      (fun n p hp => by have := abs_le.1 (hw n p hp); linarith)
      (ε := ((∫ x in c 0..c N, F x) - a) / 2) (by linarith)
    filter_upwards [this] with n hn
    linarith
  · have := weighted_prime_sum_approx_le h0 hF w E hE0 hE
      (fun n p hp => by have := abs_le.1 (hw n p hp); linarith)
      (ε := (a - (∫ x in c 0..c N, F x)) / 2) (by linarith)
    filter_upwards [this] with n hn
    linarith

/-! ### The small-prime cost (LC22, generic part) -/

/-- The primes `p ≤ δ n`. -/
noncomputable def smallPrimes (δ : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊δ * n⌋₊).filter Nat.Prime

theorem sum_log_smallPrimes {δ : ℝ} (n : ℕ) :
    ∑ p ∈ smallPrimes δ n, Real.log (p : ℝ) = Chebyshev.theta (δ * n) := rfl

theorem mem_smallPrimes {δ : ℝ} (hδ : 0 ≤ δ) {n p : ℕ} :
    p ∈ smallPrimes δ n ↔ (p : ℝ) ≤ δ * n ∧ p.Prime ∧ 0 < p := by
  simp only [smallPrimes, Finset.mem_filter, Finset.mem_Ioc]
  rw [Nat.le_floor_iff (mul_nonneg hδ n.cast_nonneg)]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, h3, h1⟩
  · rintro ⟨h2, h3, h1⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- **LC22 (generic).** Let `cost n p ≤ 12 n ⌊log_p(8n)⌋` for every prime `p ≤ δ n` (Lai Lemma 4.1 (1):
`v_p(J_n) ≥ -12 n log_p(8n)`). Then `Σ_{p ≤ δ n} cost(n,p) log p ≤ (12 δ + ε) n²` eventually, for
every `ε > 0` (Lai (5.6)-(5.7): the primes `p ≤ √(8n)` cost `O(n^{3/2} log n)`, the primes
`√(8n) < p ≤ δ n` cost at most `12 n` each, and `θ(δ n) ~ δ n`). -/
theorem small_primes_cost {δ : ℝ} (hδ : 0 < δ) (cost : ℕ → ℕ → ℝ)
    (hc : ∀ n p : ℕ, p.Prime → (p : ℝ) ≤ δ * n → cost n p ≤ 12 * n * (Nat.log p (8 * n) : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∑ p ∈ smallPrimes δ n, cost n p * Real.log (p : ℝ) ≤ (12 * δ + ε) * (n : ℝ) ^ 2 := by
  have hδ0 : 0 ≤ δ := hδ.le
  have hθ : Tendsto (fun n : ℕ => Chebyshev.theta (δ * n) / (δ * n)) atTop (𝓝 1) :=
    pnt_theta.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hδ)
  have e1 := hθ.eventually (gt_mem_nhds (show (1 : ℝ) < 1 + ε / (24 * δ) by
    have : 0 < ε / (24 * δ) := by positivity
    linarith))
  have hlog : Tendsto (fun n : ℕ => Real.log (8 * n) / (8 * (n : ℝ)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h8 : Tendsto (fun n : ℕ => 8 * (n : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
    exact ((isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero).comp h8
  have hsm : Tendsto (fun n : ℕ => 96 * (Real.log 4 / Real.log 2) *
      (Real.log (8 * n) / (8 * (n : ℝ)) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using hlog.const_mul (96 * (Real.log 4 / Real.log 2))
  have e2 := hsm.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [e1, e2, eventually_ge_atTop 1] with n h1 h2 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : (0 : ℝ) < 8 * n := by positivity
  set s : ℝ := Real.sqrt (8 * n) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hy0
  have hss : s * s = 8 * n := Real.mul_self_sqrt hy0.le
  have hsrpow : (8 * (n : ℝ)) ^ (1 / 2 : ℝ) = s := (Real.sqrt_eq_rpow _).symm
  rw [hsrpow] at h2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl8 : 0 ≤ Real.log (8 * n) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  have hsplit := Finset.sum_filter_add_sum_filter_not (smallPrimes δ n) (fun p => 8 * n < p ^ 2)
    (fun p => cost n p * Real.log (p : ℝ))
  rw [← hsplit]
  -- primes `p > √(8n)`
  have hA : ∑ p ∈ (smallPrimes δ n).filter (fun p => 8 * n < p ^ 2), cost n p * Real.log (p : ℝ) ≤
      12 * n * Chebyshev.theta (δ * n) := by
    calc ∑ p ∈ (smallPrimes δ n).filter (fun p => 8 * n < p ^ 2), cost n p * Real.log (p : ℝ)
        ≤ ∑ p ∈ (smallPrimes δ n).filter (fun p => 8 * n < p ^ 2), (12 * (n : ℝ)) * Real.log (p : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Finset.mem_filter] at hp
          obtain ⟨hp1, hp2⟩ := hp
          obtain ⟨hpd, hpp, _⟩ := (mem_smallPrimes hδ0).1 hp1
          have hlog1 : Nat.log p (8 * n) < 2 :=
            Nat.log_lt_of_lt_pow (by omega) hp2
          have hlog1' : (Nat.log p (8 * n) : ℝ) ≤ 1 := by
            have : Nat.log p (8 * n) ≤ 1 := by omega
            exact_mod_cast this
          have := hc n p hpp hpd
          have h12 : (0 : ℝ) ≤ 12 * n := by positivity
          have : cost n p ≤ 12 * n := by nlinarith
          exact mul_le_mul_of_nonneg_right this (log_nonneg_of_prime hpp)
      _ = 12 * n * ∑ p ∈ (smallPrimes δ n).filter (fun p => 8 * n < p ^ 2), Real.log (p : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ 12 * n * Chebyshev.theta (δ * n) := by
          rw [← sum_log_smallPrimes (δ := δ) n]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p hp _ =>
            log_nonneg_of_prime ((mem_smallPrimes hδ0).1 hp).2.1)
  -- primes `p ≤ √(8n)`
  have hB : ∑ p ∈ (smallPrimes δ n).filter (fun p => ¬ 8 * n < p ^ 2), cost n p * Real.log (p : ℝ) ≤
      12 * n * (Real.log (8 * n) / Real.log 2) * (Real.log 4 * s) := by
    calc ∑ p ∈ (smallPrimes δ n).filter (fun p => ¬ 8 * n < p ^ 2), cost n p * Real.log (p : ℝ)
        ≤ ∑ p ∈ (smallPrimes δ n).filter (fun p => ¬ 8 * n < p ^ 2),
            (12 * n * (Real.log (8 * n) / Real.log 2)) * Real.log (p : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Finset.mem_filter] at hp
          obtain ⟨hp1, _⟩ := hp
          obtain ⟨hpd, hpp, _⟩ := (mem_smallPrimes hδ0).1 hp1
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
          have hlp : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hp2
          have hnl : (Nat.log p (8 * n) : ℝ) ≤ Real.log (8 * n) / Real.log 2 := by
            have h1 := Real.natLog_le_logb (8 * n) p
            have h2 : Real.logb (p : ℝ) ((8 * n : ℕ) : ℝ) = Real.log (8 * n) / Real.log (p : ℝ) := by
              rw [Real.logb]; push_cast; rfl
            rw [h2] at h1
            refine h1.trans ?_
            exact div_le_div_of_nonneg_left hl8 hl2 hlp
          have := hc n p hpp hpd
          have h12 : (0 : ℝ) ≤ 12 * n := by positivity
          have : cost n p ≤ 12 * n * (Real.log (8 * n) / Real.log 2) := by
            calc cost n p ≤ 12 * n * (Nat.log p (8 * n) : ℝ) := this
              _ ≤ 12 * n * (Real.log (8 * n) / Real.log 2) := mul_le_mul_of_nonneg_left hnl h12
          exact mul_le_mul_of_nonneg_right this (log_nonneg_of_prime hpp)
      _ = 12 * n * (Real.log (8 * n) / Real.log 2) *
            ∑ p ∈ (smallPrimes δ n).filter (fun p => ¬ 8 * n < p ^ 2), Real.log (p : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ 12 * n * (Real.log (8 * n) / Real.log 2) * (Real.log 4 * s) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hsub : (smallPrimes δ n).filter (fun p => ¬ 8 * n < p ^ 2) ⊆
              (Finset.Ioc 0 ⌊s⌋₊).filter Nat.Prime := by
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨hp1, hp2⟩ := hp
            obtain ⟨_, hpp, hp0⟩ := (mem_smallPrimes hδ0).1 hp1
            rw [Finset.mem_filter, Finset.mem_Ioc]
            refine ⟨⟨hp0, ?_⟩, hpp⟩
            rw [Nat.le_floor_iff hs0.le]
            refine Real.le_sqrt_of_sq_le ?_
            have : p ^ 2 ≤ 8 * n := by omega
            exact_mod_cast this
          calc ∑ p ∈ (smallPrimes δ n).filter (fun p => ¬ 8 * n < p ^ 2), Real.log (p : ℝ)
              ≤ ∑ p ∈ (Finset.Ioc 0 ⌊s⌋₊).filter Nat.Prime, Real.log (p : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
                  log_nonneg_of_prime (Finset.mem_filter.1 hp).2)
            _ = Chebyshev.theta s := rfl
            _ ≤ Real.log 4 * s := theta_le_linear hs0.le
  -- assemble
  have hδn : (0 : ℝ) < δ * n := by positivity
  have hθb : Chebyshev.theta (δ * n) < (1 + ε / (24 * δ)) * (δ * n) := by
    have := (div_lt_iff₀ hδn).1 h1
    linarith
  have hA' : 12 * (n : ℝ) * Chebyshev.theta (δ * n) ≤ (12 * δ + ε / 2) * (n : ℝ) ^ 2 := by
    have h1' : 12 * (n : ℝ) * Chebyshev.theta (δ * n) ≤ 12 * n * ((1 + ε / (24 * δ)) * (δ * n)) :=
      mul_le_mul_of_nonneg_left hθb.le (by positivity)
    have h2' : 12 * (n : ℝ) * ((1 + ε / (24 * δ)) * (δ * n)) = (12 * δ + ε / 2) * (n : ℝ) ^ 2 := by
      field_simp
      ring
    linarith
  have hB' : 12 * (n : ℝ) * (Real.log (8 * n) / Real.log 2) * (Real.log 4 * s) ≤ ε / 2 * (n : ℝ) ^ 2 := by
    have key : 12 * (n : ℝ) * (Real.log (8 * n) / Real.log 2) * (Real.log 4 * s) =
        96 * (Real.log 4 / Real.log 2) * (Real.log (8 * n) / s) * (n : ℝ) ^ 2 := by
      field_simp
      have hs2 : s ^ 2 = 8 * n := by nlinarith [hss]
      rw [hs2]; ring
    rw [key]
    exact mul_le_mul_of_nonneg_right h2.le (by positivity)
  linarith

end CatalanCore.NT.WeightedPrimeSum


#print axioms CatalanCore.NT.WeightedPrimeSum.weighted_prime_sum_approx_le
#print axioms CatalanCore.NT.WeightedPrimeSum.weighted_prime_sum_approx_ge
#print axioms CatalanCore.NT.WeightedPrimeSum.weighted_prime_sum_approx
#print axioms CatalanCore.NT.WeightedPrimeSum.small_primes_cost
