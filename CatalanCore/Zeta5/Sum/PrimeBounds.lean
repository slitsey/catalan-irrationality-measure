module

public import CatalanCore.Zeta5.Sum.PrimeSums
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section

/-!
# ZC29: the small-prime, inner-error, inner-tail and outer-error contributions are `o(K²)`

All sums are over primes in a band `y₁ < p ≤ y₂`, weighted by `log p`; the only analytic input is
Chebyshev's bound `θ(y) ≤ log 4 · y` (`PrimeSums.theta_le_linear`).

* `band_error_bound` : `Σ_{y₁<p≤y₂} |f p| log p ≤ B · log 4 · y₂` if `|f p| ≤ B` on the band. With
  `f = w − pR(K/p)`, `B = c M³`, `y₂ = K/3` this is the inner error `O(K M³)`; with
  `f = w − K T₀(p/K)`, `B = c`, `y₂ = 2h` it is the outer error `O(K)`.
* `inner_tail_bound` : from `|R(x)| ≤ C₁(x+1)`, `Σ_{p ≤ K/T} |p R(K/p)| log p ≤ 2 C₁ log 4 · K²/T`
  uniformly in `K` (the inner tail).
* `small_primes_bound` : if `|w(K,p)| ≤ c K ⌊log_p(CK)⌋` for `p ≤ y` then
  `Σ_{p ≤ y} |w(K,p)| log p ≤ c K (log 4 · y + √(CK) log(CK))`, i.e. `O(K²/M + K^{3/2} log K)` for
  `y = K/M`.
* `small_primes_o`, `inner_error_o`, `outer_error_o`: these bounds, divided by `K²`, tend to `0`.
-/

open Filter Finset Set
open scoped Topology

set_option linter.deprecated false

namespace CatalanCore.Zeta5.Sum

open OAI.Zeta5.Workers.W14

/-- `Σ_{y₁ < p ≤ y₂} log p ≤ log 4 · y₂`. -/
lemma band_log_sum_le {y₁ y₂ : ℝ} (h12 : y₁ ≤ y₂) (hy₂ : 0 ≤ y₂) :
    ∑ p ∈ (Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊).filter Nat.Prime, Real.log (p : ℝ) ≤ Real.log 4 * y₂ := by
  have h := primeIntervalSum_eq_theta_sub h12
  unfold primeIntervalSum at h
  rw [h]
  have := Chebyshev.theta_nonneg y₁
  have := theta_le_linear hy₂
  linarith

/-- **ZC29, error bands.** If `|f p| ≤ B` for the primes of the band `y₁ < p ≤ y₂`, then
`Σ |f p| log p ≤ B log 4 · y₂`. -/
theorem band_error_bound {f : ℕ → ℝ} {y₁ y₂ B : ℝ} (hy₁ : 0 ≤ y₁) (h12 : y₁ ≤ y₂) (hB : 0 ≤ B)
    (hf : ∀ p : ℕ, p.Prime → y₁ < (p : ℝ) → (p : ℝ) ≤ y₂ → |f p| ≤ B) :
    ∑ p ∈ (Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊).filter Nat.Prime, |f p| * Real.log (p : ℝ)
      ≤ B * (Real.log 4 * y₂) := by
  have hy₂ : 0 ≤ y₂ := hy₁.trans h12
  calc ∑ p ∈ (Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊).filter Nat.Prime, |f p| * Real.log (p : ℝ)
      ≤ ∑ p ∈ (Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊).filter Nat.Prime, B * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter, Finset.mem_Ioc] at hp
        have hm := (mem_primeInterval_iff hy₁ h12 p).mpr
        have hmem := (mem_primeInterval_iff hy₁ h12 p).mp
          (by rw [Finset.mem_filter, Finset.mem_Ioc]; exact hp)
        have hlog : 0 ≤ Real.log (p : ℝ) := log_prime_nonneg hp.2
        exact mul_le_mul_of_nonneg_right (hf p hp.2 hmem.1 hmem.2.1) hlog
    _ = B * ∑ p ∈ (Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊).filter Nat.Prime, Real.log (p : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ B * (Real.log 4 * y₂) := mul_le_mul_of_nonneg_left (band_log_sum_le h12 hy₂) hB

/-- **ZC29, inner tail.** If `|R x| ≤ C₁ (x + 1)` for `x ≥ 1`, then uniformly in `K`
`Σ_{p ≤ K/T} |p R(K/p)| log p ≤ 2 C₁ log 4 · K²/T`. -/
theorem inner_tail_bound {R : ℝ → ℝ} {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hR : ∀ x : ℝ, 1 ≤ x → |R x| ≤ C₁ * (x + 1)) {K : ℕ} {T : ℝ} (hT : 1 ≤ T) :
    ∑ p ∈ (Finset.Ioc 0 ⌊(K : ℝ) / T⌋₊).filter Nat.Prime,
        |(p : ℝ) * R ((K : ℝ) / p)| * Real.log (p : ℝ)
      ≤ 2 * C₁ * Real.log 4 * ((K : ℝ) ^ 2 / T) := by
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hKT : (K : ℝ) / T ≤ K := div_le_self (Nat.cast_nonneg K) hT
  have hb := band_error_bound (f := fun p : ℕ => (p : ℝ) * R ((K : ℝ) / p))
    (y₁ := 0) (y₂ := (K : ℝ) / T) (B := 2 * C₁ * K) le_rfl (by positivity)
    (by positivity) (by
      intro p hp hp0 hpK
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      have hp0' : (0 : ℝ) < p := by linarith
      have hx : 1 ≤ (K : ℝ) / p := by
        rw [le_div_iff₀ hp0']
        have : (p : ℝ) * T ≤ K := by
          have := (le_div_iff₀ hT0).mp hpK
          linarith
        nlinarith
      have h1 := hR _ hx
      rw [abs_mul, abs_of_pos hp0']
      calc (p : ℝ) * |R ((K : ℝ) / p)| ≤ p * (C₁ * ((K : ℝ) / p + 1)) :=
            mul_le_mul_of_nonneg_left h1 hp0'.le
        _ = C₁ * (K + p) := by field_simp
        _ ≤ 2 * C₁ * K := by nlinarith)
  simp only [Nat.floor_zero] at hb
  calc _ ≤ 2 * C₁ * K * (Real.log 4 * ((K : ℝ) / T)) := hb
    _ = 2 * C₁ * Real.log 4 * ((K : ℝ) ^ 2 / T) := by ring

/-- `Σ_{p ≤ n} ⌊log_p N⌋ log p ≤ θ(n) + √N log N`. -/
lemma sum_natlog_le (N n : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.Ioc 0 n).filter Nat.Prime, (Nat.log p N : ℝ) * Real.log (p : ℝ)
      ≤ ∑ p ∈ (Finset.Ioc 0 n).filter Nat.Prime, Real.log (p : ℝ)
        + Real.sqrt N * Real.log N := by
  set S := (Finset.Ioc 0 n).filter Nat.Prime with hS
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hterm : ∀ p ∈ S, (Nat.log p N : ℝ) * Real.log (p : ℝ) ≤ Real.log (p : ℝ) +
      (if p * p ≤ N then Real.log (N : ℝ) else 0) := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    have hlogp : 0 ≤ Real.log (p : ℝ) := log_prime_nonneg hp.2
    by_cases hpp : p * p ≤ N
    · rw [if_pos hpp]
      have h1 : p ^ Nat.log p N ≤ N := Nat.pow_log_le_self p (by omega)
      have h2 : (Nat.log p N : ℝ) * Real.log (p : ℝ) ≤ Real.log (N : ℝ) := by
        rw [← Real.log_pow]
        apply Real.log_le_log (by positivity)
        exact_mod_cast h1
      linarith
    · rw [if_neg hpp]
      have h1 : Nat.log p N < 2 := Nat.log_lt_of_lt_pow (by omega) (by nlinarith [Nat.lt_of_not_le hpp])
      have h2 : (Nat.log p N : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp h1
      nlinarith
  calc ∑ p ∈ S, (Nat.log p N : ℝ) * Real.log (p : ℝ)
      ≤ ∑ p ∈ S, (Real.log (p : ℝ) + (if p * p ≤ N then Real.log (N : ℝ) else 0)) :=
        Finset.sum_le_sum hterm
    _ = ∑ p ∈ S, Real.log (p : ℝ) + ∑ p ∈ S, (if p * p ≤ N then Real.log (N : ℝ) else 0) :=
        Finset.sum_add_distrib
    _ ≤ ∑ p ∈ S, Real.log (p : ℝ) + Real.sqrt N * Real.log N := by
        gcongr
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, nsmul_eq_mul]
        have hsub : S.filter (fun p => p * p ≤ N) ⊆ Finset.Icc 1 (Nat.sqrt N) := by
          intro p hp
          rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Ioc] at hp
          rw [Finset.mem_Icc]
          exact ⟨hp.1.1.1, Nat.le_sqrt.mpr hp.2⟩
        have hc : ((S.filter (fun p => p * p ≤ N)).card : ℝ) ≤ Real.sqrt N := by
          have h1 : (S.filter (fun p => p * p ≤ N)).card ≤ Nat.sqrt N := by
            have := Finset.card_le_card hsub
            simpa using this
          have h2 : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
          calc ((S.filter (fun p => p * p ≤ N)).card : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast h1
            _ ≤ Real.sqrt N := h2
        exact mul_le_mul_of_nonneg_right hc hlogN

/-- **ZC29, small primes.** If `|w(K,p)| ≤ c K ⌊log_p(CK)⌋` for the primes `p ≤ y`, then
`Σ_{p ≤ y} |w(K,p)| log p ≤ c K (log 4 · y + √(CK) log(CK))`. -/
theorem small_primes_bound {w : ℕ → ℝ} {c : ℝ} {C K : ℕ} {y : ℝ} (hc : 0 ≤ c) (hCK : 1 ≤ C * K)
    (hy : 0 ≤ y)
    (hw : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → |w p| ≤ c * K * (Nat.log p (C * K) : ℝ)) :
    ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, |w p| * Real.log (p : ℝ)
      ≤ c * K * (Real.log 4 * y + Real.sqrt ((C * K : ℕ) : ℝ) * Real.log ((C * K : ℕ) : ℝ)) := by
  have hsum := sum_natlog_le (C * K) ⌊y⌋₊ hCK
  have hth : ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, Real.log (p : ℝ) ≤ Real.log 4 * y := by
    have := band_log_sum_le (y₁ := 0) hy hy
    simpa using this
  calc ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, |w p| * Real.log (p : ℝ)
      ≤ ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime,
          (c * K) * ((Nat.log p (C * K) : ℝ) * Real.log (p : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter, Finset.mem_Ioc] at hp
        have hpy : (p : ℝ) ≤ y := by
          have := Nat.floor_le hy
          exact (Nat.cast_le.mpr hp.1.2).trans this
        have hlog : 0 ≤ Real.log (p : ℝ) := log_prime_nonneg hp.2
        calc |w p| * Real.log (p : ℝ) ≤ (c * K * (Nat.log p (C * K) : ℝ)) * Real.log (p : ℝ) :=
              mul_le_mul_of_nonneg_right (hw p hp.2 hpy) hlog
          _ = (c * K) * ((Nat.log p (C * K) : ℝ) * Real.log (p : ℝ)) := by ring
    _ = (c * K) * ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime,
          ((Nat.log p (C * K) : ℝ) * Real.log (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (c * K) * (Real.log 4 * y + Real.sqrt ((C * K : ℕ) : ℝ) * Real.log ((C * K : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

/-! ### The `o(K²)` limits -/

lemma tendsto_sqrt_log_div (C : ℕ) (hC : 1 ≤ C) :
    Tendsto (fun K : ℕ => Real.sqrt ((C * K : ℕ) : ℝ) * Real.log ((C * K : ℕ) : ℝ) / K)
      atTop (𝓝 0) := by
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hL : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hx : Tendsto (fun K : ℕ => (C : ℝ) * K) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hC'
  have h2 := (hL.comp hx).const_mul (C : ℝ)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with K hK
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  simp only [Function.comp, Nat.cast_mul]
  have hx0 : (0 : ℝ) < (C : ℝ) * K := by positivity
  rw [Real.sqrt_eq_rpow]
  have : ((C : ℝ) * K) = ((C : ℝ) * K) ^ (1 / 2 : ℝ) * ((C : ℝ) * K) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hpos : 0 < ((C : ℝ) * K) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  field_simp
  nth_rewrite 1 [this]
  ring

/-- **ZC29, small primes are `o(K²)`:** with `y = K/M(K)`, `M → ∞`. -/
theorem small_primes_o {c : ℝ} {C : ℕ} (hC : 1 ≤ C) {M : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) :
    Tendsto (fun K : ℕ => c * K * (Real.log 4 * ((K : ℝ) / M K) +
        Real.sqrt ((C * K : ℕ) : ℝ) * Real.log ((C * K : ℕ) : ℝ)) / (K : ℝ) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun K : ℕ => Real.log 4 / M K) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hM
  have h2 := (h1.add (tendsto_sqrt_log_div C hC)).const_mul c
  simp only [add_zero, mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with K hK
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  field_simp

/-- Inner error: `c M³ · log 4 · (K/3) / K² → 0` when `M³/K → 0`. -/
theorem inner_error_o {c : ℝ} {M : ℕ → ℝ} (hM : Tendsto (fun K : ℕ => M K ^ 3 / K) atTop (𝓝 0)) :
    Tendsto (fun K : ℕ => (c * M K ^ 3) * (Real.log 4 * ((K : ℝ) / 3)) / (K : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have h := hM.const_mul (c * Real.log 4 / 3)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with K hK
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  field_simp

/-- Outer error: `c · log 4 · (a K) / K² → 0`. -/
theorem outer_error_o (c a : ℝ) :
    Tendsto (fun K : ℕ => c * (Real.log 4 * (a * K)) / (K : ℝ) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun K : ℕ => c * Real.log 4 * a * (1 / (K : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa using this.const_mul (c * Real.log 4 * a)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with K hK
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  field_simp

end CatalanCore.Zeta5.Sum
