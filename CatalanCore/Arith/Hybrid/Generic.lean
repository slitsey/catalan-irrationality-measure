module

public import CatalanCore.Arith.Hybrid.Dual3
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Route-independent pieces of the hybrid content theorem

* `extraTerm` : p = 2 correction, and all levels `e ≥ 2` (`tropExp_le`), bounded explicitly by
  `(r+m)(4 log 2 + 2 L (√(4N)+1) log(4N))`, `L = ⌊log₂ 4N⌋`, `N = r + 2m`;
* the Lemma E interface: `LemmaEHyp` and `DhybE`, the denominator with `m` removed at a set of
  primes where the Gauss valuation is known to be `≥ -(tropExp - m)`.
-/

open Finset

namespace CatalanCore.Arith.Hybrid

/-- The part of `tropExp` that is not the level-1 dual. -/
noncomputable def extraTerm (r m p : ℕ) : ℕ :=
  cOf p * (r + m) + 2 * (r + m) *
    ((Finset.Icc 2 (Elev r m)).filter (fun e => p ^ e ≤ 4 * (r + 2 * m))).card

theorem tropExp_le' (r m p : ℕ) (hr : 1 ≤ r) (hp : p.Prime) :
    tropExp r m p ≤ tropVal (HW p r m) + extraTerm r m p := by
  have := tropExp_le r m p hr hp
  unfold extraTerm; omega

lemma cnt_le (r m p : ℕ) (hp : p.Prime) :
    ((Finset.Icc 2 (Elev r m)).filter (fun e => p ^ e ≤ 4 * (r + 2 * m))).card ≤
      Nat.log 2 (4 * (r + 2 * m)) := by
  calc _ ≤ (Finset.Icc 2 (Nat.log 2 (4 * (r + 2 * m)))).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
        have h2 := Finset.mem_Icc.mp he1
        refine Finset.mem_Icc.mpr ⟨h2.1, ?_⟩
        apply Nat.le_log_of_pow_le (by norm_num)
        exact (Nat.pow_le_pow_left hp.two_le e).trans he2
    _ ≤ _ := by simp

lemma cnt_eq_zero_of_large (r m p : ℕ) (hp : p.Prime) (h : 4 * (r + 2 * m) < p ^ 2) :
    ((Finset.Icc 2 (Elev r m)).filter (fun e => p ^ e ≤ 4 * (r + 2 * m))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hle
  have h2 := (Finset.mem_Icc.mp he).1
  have : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos h2
  omega

/-- Finite bound on the extra terms, weighted by `log p`. -/
theorem extra_sum_le (r m : ℕ) :
    ∑ p ∈ (Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime,
        (extraTerm r m p : ℝ) * Real.log p ≤
      (r + m : ℝ) * (4 * Real.log 2 + 2 * (Nat.log 2 (4 * (r + 2 * m)) : ℝ) *
        ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) * Real.log (4 * (r + 2 * m) + 2)) := by
  set P := (Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime with hP
  set L : ℝ := (Nat.log 2 (4 * (r + 2 * m)) : ℝ)
  have hsplit : ∀ p ∈ P, (extraTerm r m p : ℝ) * Real.log p ≤
      (if p = 2 then 4 * (r + m : ℝ) * Real.log 2 else 0) +
      (if p ≤ Nat.sqrt (4 * (r + 2 * m)) then 2 * (r + m : ℝ) * L * Real.log (4 * (r + 2 * m) + 2) else 0) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hpl := (Finset.mem_filter.mp hp).1
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hlogle : Real.log p ≤ Real.log (4 * (r + 2 * m) + 2) := by
      apply Real.log_le_log (by exact_mod_cast hpp.pos)
      have := Finset.mem_range.mp hpl
      have : (p : ℝ) ≤ 4 * (r + 2 * m) + 2 := by exact_mod_cast (by omega : p ≤ 4 * (r + 2 * m) + 2)
      exact_mod_cast this
    have hcnt := cnt_le r m p hpp
    unfold extraTerm
    push_cast
    have hc : ((cOf p : ℕ) : ℝ) * (r + m) * Real.log p ≤ if p = 2 then 4 * (r + m : ℝ) * Real.log 2 else 0 := by
      unfold cOf; split_ifs with h
      · subst h; norm_num
      · simp
    have hq : (2 * (r + m : ℝ)) * (((Finset.Icc 2 (Elev r m)).filter (fun e => p ^ e ≤ 4 * (r + 2 * m))).card : ℝ)
        * Real.log p ≤ if p ≤ Nat.sqrt (4 * (r + 2 * m)) then 2 * (r + m : ℝ) * L * Real.log (4 * (r + 2 * m) + 2) else 0 := by
      split_ifs with h
      · have h1 : ((((Finset.Icc 2 (Elev r m)).filter (fun e => p ^ e ≤ 4 * (r + 2 * m))).card : ℕ) : ℝ) ≤ L := by
          exact (Nat.cast_le (α := ℝ)).mpr hcnt
        have hrm : (0 : ℝ) ≤ 2 * (r + m : ℝ) := by positivity
        calc _ ≤ (2 * (r + m : ℝ)) * L * Real.log (4 * (r + 2 * m) + 2) := by
              apply mul_le_mul _ hlogle hlog (by positivity)
              exact mul_le_mul_of_nonneg_left h1 hrm
          _ = _ := by ring
      · have : p ^ 2 > 4 * (r + 2 * m) := by
          by_contra hh
          push_neg at hh
          exact h (Nat.le_sqrt'.mpr (by nlinarith))
        rw [cnt_eq_zero_of_large r m p hpp this]; simp
    nlinarith [hc, hq]
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ p ∈ P, (if p = 2 then 4 * (r + m : ℝ) * Real.log 2 else 0) ≤ 4 * (r + m : ℝ) * Real.log 2 := by
    rw [← Finset.sum_filter]
    have : (P.filter (fun p => p = 2)) ⊆ {2} := by
      intro x hx; simp at hx ⊢; exact hx.2
    calc _ ≤ ∑ p ∈ ({2} : Finset ℕ), 4 * (r + m : ℝ) * Real.log 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg this
          intro _ _ _; positivity
      _ = _ := by simp
  have h2 : ∑ p ∈ P, (if p ≤ Nat.sqrt (4 * (r + 2 * m)) then 2 * (r + m : ℝ) * L * Real.log (4 * (r + 2 * m) + 2) else 0)
      ≤ ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) * (2 * (r + m : ℝ) * L * Real.log (4 * (r + 2 * m) + 2)) := by
    rw [← Finset.sum_filter]
    have hsub : P.filter (fun p => p ≤ Nat.sqrt (4 * (r + 2 * m))) ⊆ Finset.range (Nat.sqrt (4 * (r + 2 * m)) + 1) := by
      intro x hx; simp at hx ⊢; omega
    have hnn : 0 ≤ 2 * (r + m : ℝ) * L * Real.log (4 * (r + 2 * m) + 2) := by
      apply mul_nonneg (by positivity)
      apply Real.log_nonneg; have : (0:ℝ) ≤ 4 * (r + 2 * m) := by positivity
      linarith
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hnn
    have := Finset.card_le_card hsub
    simp only [Finset.card_range] at this
    exact_mod_cast this
  nlinarith [h1, h2]

/-! ### The extra terms are `o(r²)` -/

open Filter Topology

lemma asymp_aux : Tendsto (fun x : ℝ => 8 / x + 160 * (Real.log x) ^ 2 * Real.sqrt x / x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => 8 / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun x : ℝ => 8 / x + 10240 * x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := 1 / 4) (by norm_num)).const_mul 10240
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
    calc 8 / x + 160 * (Real.log x) ^ 2 * Real.sqrt x / x
        ≤ 8 / x + 160 * (64 * x ^ (1 / 4 : ℝ)) * Real.sqrt x / x := by
          gcongr
      _ = 8 / x + 10240 * (x ^ (1 / 4 : ℝ) * Real.sqrt x / x) := by ring
      _ = _ := by rw [hkey]

/-- The explicit extra bound. -/
noncomputable def extraBound (r m : ℕ) : ℝ :=
  (r + m : ℝ) * (4 * Real.log 2 + 2 * (Nat.log 2 (4 * (r + 2 * m)) : ℝ) *
        ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) * Real.log (4 * (r + 2 * m) + 2))

lemma extraBound_le (r m : ℕ) (hr : 14 ≤ r) (hm : m ≤ r) :
    extraBound r m ≤ (r : ℝ) ^ 2 * (8 / r + 160 * (Real.log r) ^ 2 * Real.sqrt r / r) := by
  have hx : (14 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 : (0 : ℝ) < r := by linarith
  have hmr : (m : ℝ) ≤ r := by exact_mod_cast hm
  have hlx : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  have hN : ((4 * (r + 2 * m) : ℕ) : ℝ) ≤ 12 * r := by push_cast; linarith
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hl2' : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  -- log 12 r ≤ 2 log r, log 14 r ≤ 2 log r
  have hlog14 : Real.log (14 * r) ≤ 2 * Real.log r := by
    rw [show (2 : ℝ) * Real.log r = Real.log (r ^ 2) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlogN : Real.log (((4 * (r + 2 * m) : ℕ) : ℝ)) ≤ 2 * Real.log r := by
    refine le_trans (Real.log_le_log (by positivity) (hN.trans (by linarith : 12 * (r : ℝ) ≤ 14 * r))) hlog14
  have hL : (Nat.log 2 (4 * (r + 2 * m)) : ℝ) ≤ 4 * Real.log r := by
    have h1 := Real.natLog_le_logb (4 * (r + 2 * m)) 2
    have h2 : Real.logb 2 ((4 * (r + 2 * m) : ℕ) : ℝ) ≤ 4 * Real.log r := by
      rw [Real.logb]
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hlogN, hl2', hlx]
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
  have hlogA : Real.log (4 * ((r : ℝ) + 2 * m) + 2) ≤ 2 * Real.log r := by
    refine le_trans (Real.log_le_log (by positivity) (show 4 * ((r : ℝ) + 2 * m) + 2 ≤ 14 * r by nlinarith)) hlog14
  unfold extraBound
  have hsq := Real.sqrt_nonneg (r : ℝ)
  have hLnn : (0 : ℝ) ≤ (Nat.log 2 (4 * (r + 2 * m)) : ℝ) := by positivity
  have hSnn : (0 : ℝ) ≤ (Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1 := by positivity
  have hlognn : 0 ≤ Real.log (4 * ((r : ℝ) + 2 * m) + 2) := Real.log_nonneg (by nlinarith)
  have hprod : 2 * (Nat.log 2 (4 * (r + 2 * m)) : ℝ) * ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) *
      Real.log (4 * ((r : ℝ) + 2 * m) + 2) ≤ 2 * (4 * Real.log r) * (5 * Real.sqrt r) * (2 * Real.log r) := by
    gcongr
  have h4 : (4 * Real.log 2) ≤ 4 := by linarith
  have e : (r : ℝ) ^ 2 * (8 / r + 160 * (Real.log r) ^ 2 * Real.sqrt r / r) =
      8 * r + 160 * r * (Real.log r) ^ 2 * Real.sqrt r := by field_simp
  rw [e]
  have : ((r : ℝ) + m) * (4 * Real.log 2 + 2 * (Nat.log 2 (4 * (r + 2 * m)) : ℝ) * ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) *
      Real.log (4 * ((r : ℝ) + 2 * m) + 2)) ≤ (2 * r) * (4 + 80 * (Real.log r) ^ 2 * Real.sqrt r) := by
    apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
    nlinarith [hprod]
  push_cast at this ⊢
  nlinarith [this]

/-- **The extra terms are negligible.**  For every `ε > 0`, eventually in `r`, for every `m ≤ r`,
the bound of `extra_sum_le` is at most `ε r²`. -/
theorem extra_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m ≤ r, extraBound r m ≤ ε * (r : ℝ) ^ 2 := by
  have h := (asymp_aux.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hε)
  filter_upwards [h, eventually_ge_atTop 14] with r hr h14 m hm
  have := extraBound_le r m h14 hm
  simp only [Function.comp] at hr
  have hr2 : (0 : ℝ) ≤ (r : ℝ) ^ 2 := by positivity
  nlinarith

end CatalanCore.Arith.Hybrid
