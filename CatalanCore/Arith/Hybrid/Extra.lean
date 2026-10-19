module

public import CatalanCore.Arith.Hybrid.Levels
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The negligible terms: bad primes, higher levels

`ex_sum_bound`: if the primes carry an extra weight `exG p ≤ 2(r+m)·Lg`, vanishing unless
`p² ≤ L N` (`N = r + 2m`), then `∑_{p < Bd} exG p · log p ≤ (√(L N)+1) · 2(r+m) Lg · log (L N+5)`.
`extraG L E c β r m` is this bound plus the bad-prime part `(r+m)(c + 2 log₂ E(N)) β`
(`c` bounds the normalisation exponents `cOf`, `β` is the sum of `log b` over the bad primes,
`E N` bounds `Ebd N + N`).  It is monotone in all parameters.
`extra_small` / `extraG_small`: for `L ≤ 4`, `c ≤ 4`, `E N ≤ 5 N³`, `β ≤ 3 log 2` the expression is
`≤ ε r²` eventually, uniformly in `m ≤ r`; this covers λ, the mirror and the L(2, χ₋₃) frame.
-/

open Finset Filter Topology

namespace CatalanCore.Arith.Hybrid

theorem ex_sum_bound (r m Bd Lc : ℕ) (hBd : Bd ≤ Lc * (r + 2 * m) + 5)
    (exG : ℕ → ℕ) (Lg : ℕ)
    (hexG : ∀ p, p.Prime → exG p ≤ 2 * (r + m) * Lg)
    (hexG0 : ∀ p, p.Prime → Lc * (r + 2 * m) < p ^ 2 → exG p = 0) :
    ∑ p ∈ (range Bd).filter Nat.Prime, (exG p : ℝ) * Real.log p ≤
      ((Nat.sqrt (Lc * (r + 2 * m)) : ℝ) + 1) *
        (2 * (r + m : ℝ) * Lg * Real.log ((Lc : ℝ) * (r + 2 * m) + 5)) := by
  set P := (range Bd).filter Nat.Prime with hP
  have hsplit : ∀ p ∈ P, (exG p : ℝ) * Real.log p ≤
      (if p ≤ Nat.sqrt (Lc * (r + 2 * m)) then
        2 * (r + m : ℝ) * Lg * Real.log ((Lc : ℝ) * (r + 2 * m) + 5) else 0) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hpl := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hlogle : Real.log p ≤ Real.log ((Lc : ℝ) * (r + 2 * m) + 5) := by
      apply Real.log_le_log (by exact_mod_cast hpp.pos)
      have : (p : ℝ) ≤ (Lc : ℝ) * (r + 2 * m) + 5 := by
        exact_mod_cast (by omega : p ≤ Lc * (r + 2 * m) + 5)
      exact this
    split_ifs with h
    · have h1 : (exG p : ℝ) ≤ 2 * (r + m : ℝ) * Lg := by exact_mod_cast hexG p hpp
      exact mul_le_mul h1 hlogle hlog (by positivity)
    · have : p ^ 2 > Lc * (r + 2 * m) := by
        by_contra hh
        push_neg at hh
        exact h (Nat.le_sqrt'.mpr hh)
      rw [hexG0 p hpp this]; simp
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [← Finset.sum_filter]
  have hsub : P.filter (fun p => p ≤ Nat.sqrt (Lc * (r + 2 * m))) ⊆
      Finset.range (Nat.sqrt (Lc * (r + 2 * m)) + 1) := by
    intro x hx; simp at hx ⊢; omega
  have hnn : 0 ≤ 2 * (r + m : ℝ) * Lg * Real.log ((Lc : ℝ) * (r + 2 * m) + 5) := by
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (Lc : ℝ) * (r + 2 * m) := by positivity
    linarith
  rw [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hnn
  have := Finset.card_le_card hsub
  simp only [Finset.card_range] at this
  exact_mod_cast this

lemma asymp_aux : Tendsto (fun x : ℝ => 8 / x + 200 * (Real.log x) ^ 2 * Real.sqrt x / x) atTop
    (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => 8 / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun x : ℝ => 8 / x + 12800 * x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := 1 / 4) (by norm_num)).const_mul 12800
    simpa using h1.add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have := Real.sqrt_nonneg x
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have hl : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by
      have := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 8 by norm_num)
      linarith [show x ^ (1 / 8 : ℝ) / (1 / 8) = 8 * x ^ (1 / 8 : ℝ) by field_simp]
    have hl2 : (Real.log x) ^ 2 ≤ 64 * x ^ (1 / 4 : ℝ) := by
      have e : (x ^ (1 / 8 : ℝ)) ^ 2 = x ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
      nlinarith [hl, hl0, e]
    have hs : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    have hkey : x ^ (1 / 4 : ℝ) * Real.sqrt x / x = x ^ (-(1 / 4 : ℝ)) := by
      rw [hs, ← Real.rpow_add hx0]
      have : x ^ ((1 / 4 : ℝ) + 1 / 2) / x = x ^ ((1 / 4 : ℝ) + 1 / 2 - 1) :=
        (Real.rpow_sub_one hx0.ne' _).symm
      rw [this]; norm_num
    have hsq := Real.sqrt_nonneg x
    calc 8 / x + 200 * (Real.log x) ^ 2 * Real.sqrt x / x
        ≤ 8 / x + 200 * (64 * x ^ (1 / 4 : ℝ)) * Real.sqrt x / x := by gcongr
      _ = 8 / x + 12800 * (x ^ (1 / 4 : ℝ) * Real.sqrt x / x) := by ring
      _ = _ := by rw [hkey]

/-- The negligible terms for the numerology `(L, E, c, β)`. -/
noncomputable def extraG (Lc : ℕ) (E : ℕ → ℕ) (cm : ℕ) (β : ℝ) (r m : ℕ) : ℝ :=
  (r + m : ℝ) * (cm + 2 * (Nat.log 2 (E (r + 2 * m)) : ℝ)) * β +
  ((Nat.sqrt (Lc * (r + 2 * m)) : ℝ) + 1) *
    (2 * (r + m : ℝ) * (Nat.log 2 (Lc * (r + 2 * m)) : ℝ) * Real.log ((Lc : ℝ) * (r + 2 * m) + 5))

lemma extraG_mono {Lc Lc' : ℕ} {E E' : ℕ → ℕ} {cm cm' : ℕ} {β β' : ℝ} (hL : Lc ≤ Lc')
    (hE : ∀ N, E N ≤ E' N) (hc : cm ≤ cm') (hβ : β ≤ β') (hβ0 : 0 ≤ β) (r m : ℕ) :
    extraG Lc E cm β r m ≤ extraG Lc' E' cm' β' r m := by
  unfold extraG
  have hl1 : (Nat.log 2 (E (r + 2 * m)) : ℝ) ≤ Nat.log 2 (E' (r + 2 * m)) := by
    exact_mod_cast Nat.log_mono_right (hE _)
  have hc' : (cm : ℝ) ≤ cm' := by exact_mod_cast hc
  have hs : ((Nat.sqrt (Lc * (r + 2 * m)) : ℕ) : ℝ) ≤ Nat.sqrt (Lc' * (r + 2 * m)) := by
    exact_mod_cast Nat.sqrt_le_sqrt (Nat.mul_le_mul_right _ hL)
  have hl2 : (Nat.log 2 (Lc * (r + 2 * m)) : ℝ) ≤ Nat.log 2 (Lc' * (r + 2 * m)) := by
    exact_mod_cast Nat.log_mono_right (Nat.mul_le_mul_right _ hL)
  have hLL : (Lc : ℝ) ≤ Lc' := by exact_mod_cast hL
  have hlog : Real.log ((Lc : ℝ) * (r + 2 * m) + 5) ≤ Real.log ((Lc' : ℝ) * (r + 2 * m) + 5) := by
    apply Real.log_le_log (by positivity)
    have : (0 : ℝ) ≤ r + 2 * m := by positivity
    nlinarith
  have hlogn : 0 ≤ Real.log ((Lc : ℝ) * (r + 2 * m) + 5) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ (Lc : ℝ) * (r + 2 * m) := by positivity
                        linarith)
  have hA : (r + m : ℝ) * (cm + 2 * (Nat.log 2 (E (r + 2 * m)) : ℝ)) * β ≤
      (r + m : ℝ) * (cm' + 2 * (Nat.log 2 (E' (r + 2 * m)) : ℝ)) * β' := by
    have h1 : (cm + 2 * (Nat.log 2 (E (r + 2 * m)) : ℝ)) ≤
        (cm' + 2 * (Nat.log 2 (E' (r + 2 * m)) : ℝ)) := by linarith
    have h2 : (0 : ℝ) ≤ (r + m : ℝ) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 h2) hβ hβ0 (by positivity)
  have hB : ((Nat.sqrt (Lc * (r + 2 * m)) : ℝ) + 1) *
      (2 * (r + m : ℝ) * (Nat.log 2 (Lc * (r + 2 * m)) : ℝ) *
        Real.log ((Lc : ℝ) * (r + 2 * m) + 5)) ≤
      ((Nat.sqrt (Lc' * (r + 2 * m)) : ℝ) + 1) *
        (2 * (r + m : ℝ) * (Nat.log 2 (Lc' * (r + 2 * m)) : ℝ) *
          Real.log ((Lc' : ℝ) * (r + 2 * m) + 5)) := by
    have hn : (0 : ℝ) ≤ 2 * (r + m : ℝ) := by positivity
    refine mul_le_mul (by linarith) ?_ (by positivity) (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hl2 hn) hlog hlogn (by positivity)
  linarith

/-- The explicit extra bound: the `(L, E, c, β) = (4, 5N³, 4, log 2)` numerology, which dominates
that of λ, the mirror and the L(2, χ₋₃) frame. -/
noncomputable def extraBound (r m : ℕ) : ℝ :=
  extraG 4 (fun N => 5 * N ^ 3) 4 (Real.log 2) r m

lemma extraBound_eq (r m : ℕ) : extraBound r m =
    (r + m : ℝ) * (4 + 2 * (Nat.log 2 (5 * (r + 2 * m) ^ 3) : ℝ)) * Real.log 2 +
  ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) *
    (2 * (r + m : ℝ) * (Nat.log 2 (4 * (r + 2 * m)) : ℝ) * Real.log (4 * (r + 2 * m) + 5)) := by
  unfold extraBound extraG
  push_cast
  rfl

lemma extraBound_le (r m : ℕ) (hr : 14 ≤ r) (hm : m ≤ r) :
    extraBound r m ≤ (r : ℝ) ^ 2 * (8 / r + 200 * (Real.log r) ^ 2 * Real.sqrt r / r) := by
  have hx : (14 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 : (0 : ℝ) < r := by linarith
  have hmr : (m : ℝ) ≤ r := by exact_mod_cast hm
  have hlx : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hl2' : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hN : ((4 * (r + 2 * m) : ℕ) : ℝ) ≤ 12 * r := by push_cast; linarith
  have hlog14 : Real.log (14 * r) ≤ 2 * Real.log r := by
    rw [show (2 : ℝ) * Real.log r = Real.log (r ^ 2) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlogN : Real.log (((4 * (r + 2 * m) : ℕ) : ℝ)) ≤ 2 * Real.log r :=
    le_trans (Real.log_le_log (by positivity) (hN.trans (by linarith : 12 * (r : ℝ) ≤ 14 * r)))
      hlog14
  have hL : (Nat.log 2 (4 * (r + 2 * m)) : ℝ) ≤ 4 * Real.log r := by
    have h1 := Real.natLog_le_logb (4 * (r + 2 * m)) 2
    have h2 : Real.logb 2 ((4 * (r + 2 * m) : ℕ) : ℝ) ≤ 4 * Real.log r := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith [hlogN, hl2', hlx]
    exact h1.trans h2
  have hNN : ((5 * (r + 2 * m) ^ 3 : ℕ) : ℝ) ≤ (r : ℝ) ^ 5 := by
    push_cast
    have h3 : (r : ℝ) + 2 * m ≤ 3 * r := by linarith
    have h0 : (0 : ℝ) ≤ (r : ℝ) + 2 * m := by positivity
    have h4 : ((r : ℝ) + 2 * m) ^ 3 ≤ (3 * r) ^ 3 := pow_le_pow_left₀ h0 h3 3
    have h5 : (196 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have h6 : (196 : ℝ) * (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 5 := by
      have := mul_le_mul_of_nonneg_right h5 (pow_nonneg hx0.le 3)
      nlinarith
    nlinarith [pow_nonneg hx0.le 3]
  have hLb : (Nat.log 2 (5 * (r + 2 * m) ^ 3) : ℝ) ≤ 10 * Real.log r := by
    have h1 := Real.natLog_le_logb (5 * (r + 2 * m) ^ 3) 2
    have h2 : Real.logb 2 ((5 * (r + 2 * m) ^ 3 : ℕ) : ℝ) ≤ 10 * Real.log r := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      have : Real.log (((5 * (r + 2 * m) ^ 3 : ℕ) : ℝ)) ≤ 5 * Real.log r := by
        rw [show (5 : ℝ) * Real.log r = Real.log ((r : ℝ) ^ 5) by rw [Real.log_pow]; norm_num]
        exact Real.log_le_log (by positivity) hNN
      nlinarith [hlx]
    exact h1.trans h2
  have hS : ((Nat.sqrt (4 * (r + 2 * m)) : ℕ) : ℝ) + 1 ≤ 5 * Real.sqrt r := by
    have h1 := Real.nat_sqrt_le_real_sqrt (a := 4 * (r + 2 * m))
    have h2 : Real.sqrt ((4 * (r + 2 * m) : ℕ) : ℝ) ≤ 4 * Real.sqrt r := by
      calc _ ≤ Real.sqrt (16 * r) := Real.sqrt_le_sqrt (by push_cast at hN ⊢; linarith)
        _ = 4 * Real.sqrt r := by
          rw [Real.sqrt_mul (by norm_num)]
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h3 : (1 : ℝ) ≤ Real.sqrt r := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have hlogA : Real.log (4 * ((r : ℝ) + 2 * m) + 5) ≤ 2 * Real.log r :=
    le_trans (Real.log_le_log (by positivity)
      (show 4 * ((r : ℝ) + 2 * m) + 5 ≤ 14 * r by nlinarith)) hlog14
  rw [extraBound_eq]
  have hsq := Real.sqrt_nonneg (r : ℝ)
  have hLnn : (0 : ℝ) ≤ (Nat.log 2 (4 * (r + 2 * m)) : ℝ) := by positivity
  have hSnn : (0 : ℝ) ≤ (Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1 := by positivity
  have hlognn : 0 ≤ Real.log (4 * ((r : ℝ) + 2 * m) + 5) := Real.log_nonneg (by nlinarith)
  have hprod : 2 * (Nat.log 2 (4 * (r + 2 * m)) : ℝ) * ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) *
      Real.log (4 * ((r : ℝ) + 2 * m) + 5) ≤
      2 * (4 * Real.log r) * (5 * Real.sqrt r) * (2 * Real.log r) := by gcongr
  have e : (r : ℝ) ^ 2 * (8 / r + 200 * (Real.log r) ^ 2 * Real.sqrt r / r) =
      8 * r + 200 * r * (Real.log r) ^ 2 * Real.sqrt r := by field_simp
  rw [e]
  have hsr : (1 : ℝ) ≤ Real.sqrt r := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hlr : 1 ≤ Real.log r := by
    have h14 : Real.exp 1 ≤ 14 := by
      have := Real.exp_one_lt_d9; linarith
    by_contra hh
    push_neg at hh
    have : (r : ℝ) < Real.exp 1 := by
      rw [← Real.exp_log hx0]; exact Real.exp_lt_exp.mpr hh
    linarith
  have t1 : ((r : ℝ) + m) *
      (4 + 2 * (Nat.log 2 (5 * (r + 2 * m) ^ 3) : ℝ)) * Real.log 2 ≤
      (2 * r) * (4 + 20 * Real.log r) := by
    have hrm : ((r : ℝ) + m) ≤ 2 * r := by linarith
    have : (4 + 2 * (Nat.log 2 (5 * (r + 2 * m) ^ 3) : ℝ)) ≤
        4 + 20 * Real.log r := by linarith
    calc _ ≤ ((r : ℝ) + m) * (4 + 20 * Real.log r) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left this (by positivity)) hl2.le
            (Real.log_nonneg (by norm_num)) (by positivity)
      _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hrm (by positivity)
  have t2 : ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) *
      (2 * (r + m : ℝ) * (Nat.log 2 (4 * (r + 2 * m)) : ℝ) *
        Real.log (4 * ((r : ℝ) + 2 * m) + 5)) ≤
      (2 * r) * (80 * (Real.log r) ^ 2 * Real.sqrt r) := by
    have hrm : ((r : ℝ) + m) ≤ 2 * r := by linarith
    calc _ = ((r : ℝ) + m) * (2 * (Nat.log 2 (4 * (r + 2 * m)) : ℝ) *
          ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) * Real.log (4 * ((r : ℝ) + 2 * m) + 5)) := by
            ring
      _ ≤ (2 * r) * (2 * (4 * Real.log r) * (5 * Real.sqrt r) * (2 * Real.log r)) :=
          mul_le_mul hrm hprod (by positivity) (by positivity)
      _ = _ := by ring
  have t3 : (2 * (r : ℝ)) * (4 + 20 * Real.log r) ≤
      8 * r + 40 * r * (Real.log r) ^ 2 * Real.sqrt r := by
    have : Real.log r ≤ (Real.log r) ^ 2 * Real.sqrt r := by nlinarith
    nlinarith
  push_cast at t1 t2 ⊢
  nlinarith [t1, t2, t3]

/-- **The negligible terms are `o(r²)`.** -/
theorem extra_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m ≤ r, extraBound r m ≤ ε * (r : ℝ) ^ 2 := by
  have h := (asymp_aux.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hε)
  filter_upwards [h, eventually_ge_atTop 14] with r hr h14 m hm
  have := extraBound_le r m h14 hm
  simp only [Function.comp] at hr
  have hr2 : (0 : ℝ) ≤ (r : ℝ) ^ 2 := by positivity
  nlinarith

lemma extraBound_three (r m : ℕ) :
    extraG 4 (fun N => 5 * N ^ 3) 4 (3 * Real.log 2) r m ≤ 3 * extraBound r m := by
  unfold extraBound extraG
  push_cast
  have hl : 0 ≤ Real.log (4 * ((r : ℝ) + 2 * m) + 5) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ 4 * ((r : ℝ) + 2 * m) := by positivity
                        linarith)
  have hS : 0 ≤ ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) *
      (2 * (r + m : ℝ) * (Nat.log 2 (4 * (r + 2 * m)) : ℝ) * Real.log (4 * ((r : ℝ) + 2 * m) + 5)) := by
    positivity
  nlinarith

/-- **Negligibility for every numerology dominated by `(4, 5N³, 4, 3 log 2)`.** -/
theorem extraG_small {Lc : ℕ} {E : ℕ → ℕ} {cm : ℕ} {β : ℝ} (hL : Lc ≤ 4)
    (hE : ∀ N, E N ≤ 5 * N ^ 3) (hc : cm ≤ 4) (hβ0 : 0 ≤ β) (hβ : β ≤ 3 * Real.log 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m ≤ r, extraG Lc E cm β r m ≤ ε * (r : ℝ) ^ 2 := by
  filter_upwards [extra_small (ε / 3) (by positivity)] with r hr m hm
  have h1 := extraG_mono hL hE hc hβ hβ0 r m
  have h2 := extraBound_three r m
  have h3 := hr m hm
  linarith

end CatalanCore.Arith.Hybrid
