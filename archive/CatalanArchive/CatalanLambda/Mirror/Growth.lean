module

public import CatalanArchive.CatalanLambda.Mirror.Integrality
public import CatalanArchive.CatalanLambda.Growth
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Mirror constant: growth of `log D_h`

Reduction to a Chebyshev-type upper bound for `θ(x; 4, a)`; same constant `313/105` with the
classes swapped (class `1` now carries `21/10`, class `3` carries `37/42`).
-/

open Finset Classical Filter

namespace CatalanLambda.Mirror

open CatalanLambda (th th_nonneg sum_range_cast sum_max_le ev_log_le ev_log_sq_le)

/-- thresholds: class `1` -/
def T1 (h a : ℕ) : ℕ := max (4 * a) (h - 1 - a)
/-- thresholds: class `3` -/
def T3 (h a : ℕ) : ℕ := max ((4 * a) / 3) (h - 1 - a)

/-- the set of active odd prime powers at `a` -/
noncomputable def FaSet (h a : ℕ) : Finset ℕ := (Qset h).filter (fun q => uq h q a)

lemma prime_part (h a : ℕ) :
    ∑ q ∈ (FaSet h a).filter Nat.Prime, Real.log q ≤ th 1 (T1 h a) + th 3 (T3 h a) := by
  set S1 := (Finset.range (T1 h a + 1)).filter (fun n => n.Prime ∧ n % 4 = 1)
  set S3 := (Finset.range (T3 h a + 1)).filter (fun n => n.Prime ∧ n % 4 = 3)
  have hdisj : Disjoint S1 S3 := by
    rw [Finset.disjoint_left]
    intro n h3 h1
    have := (Finset.mem_filter.mp h3).2.2
    have := (Finset.mem_filter.mp h1).2.2
    omega
  have hsub : (FaSet h a).filter Nat.Prime ⊆ S1 ∪ S3 := by
    intro q hq
    simp only [FaSet, Qset, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨⟨⟨hq4, hpp, hodd, h3d⟩, hu⟩, hqp⟩ := hq
    have hq2 : q % 2 = 1 := Nat.odd_iff.mp hodd
    simp only [Finset.mem_union, S3, S1, Finset.mem_filter, Finset.mem_range]
    by_cases h1 : q % 4 = 1
    · left
      have hj : jq q = 1 := by simp [jq, h1]
      unfold uq kq at hu
      rw [hj] at hu
      unfold T1
      refine ⟨by omega, hqp, h1⟩
    · right
      have h3 : q % 4 = 3 := by omega
      have hj : jq q = 3 := by simp [jq, h1]
      unfold uq kq at hu
      rw [hj] at hu
      unfold T3
      refine ⟨by omega, hqp, h3⟩
  calc ∑ q ∈ (FaSet h a).filter Nat.Prime, Real.log q
      ≤ ∑ q ∈ S1 ∪ S3, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n hn _
        rcases Finset.mem_union.mp hn with h | h <;>
          exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp h).2.1.one_lt.le)
    _ = th 1 (T1 h a) + th 3 (T3 h a) := by
        rw [Finset.sum_union hdisj]; rfl

/-- non-prime odd prime powers `≤ 4h` -/
noncomputable def Qnp (h : ℕ) : Finset ℕ := (Qset h).filter (fun q => ¬ q.Prime)

lemma nonprime_part (h a : ℕ) (hh : 1 ≤ h) :
    ∑ q ∈ (FaSet h a).filter (fun q => ¬ q.Prime), Real.log (q.minFac : ℝ)
      ≤ (Qnp h).card * Real.log (4 * h) := by
  have h4 : (1 : ℝ) ≤ 4 * h := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  calc ∑ q ∈ (FaSet h a).filter (fun q => ¬ q.Prime), Real.log (q.minFac : ℝ)
      ≤ ∑ q ∈ (FaSet h a).filter (fun q => ¬ q.Prime), Real.log (4 * h : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        simp only [FaSet, Qset, Finset.mem_filter, Finset.mem_range] at hq
        obtain ⟨⟨⟨hq4, hpp, hodd, h3d⟩, hu⟩, hqp⟩ := hq
        have hqpos : 0 < q := hpp.pos
        have : q.minFac ≤ q := Nat.minFac_le hqpos
        apply Real.log_le_log (by exact_mod_cast Nat.minFac_pos q)
        have : (q.minFac : ℝ) ≤ (4 * h : ℕ) := by exact_mod_cast (by omega : q.minFac ≤ 4 * h)
        simpa using this
    _ ≤ ∑ q ∈ Qnp h, Real.log (4 * h : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          simp only [FaSet, Qnp, Finset.mem_filter] at hq ⊢
          exact ⟨hq.1.1, hq.2⟩
        · intros; exact Real.log_nonneg h4
    _ = (Qnp h).card * Real.log (4 * h) := by
        rw [Finset.sum_const, nsmul_eq_mul]

lemma log_W (h a : ℕ) :
    Real.log (W h a) = Real.log 4 + (Nat.log 2 h) * Real.log 2 +
      (Nat.log 3 (12 * h)) * Real.log 3 +
      ∑ q ∈ FaSet h a, Real.log (q.minFac : ℝ) := by
  have hq : ∀ q ∈ FaSet h a, (q.minFac : ℝ) ≠ 0 := fun q _ => by
    exact_mod_cast (Nat.minFac_pos q).ne'
  have : (W h a : ℝ) = 4 * ((2 ^ Nat.log 2 h * 3 ^ Nat.log 3 (12 * h)) *
      ∏ q ∈ FaSet h a, (q.minFac : ℝ)) := by
    unfold W Wm Wodd FaSet
    push_cast
    rfl
  have hprod : (∏ q ∈ FaSet h a, (q.minFac : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hq
  have h23 : ((2 : ℝ) ^ Nat.log 2 h * 3 ^ Nat.log 3 (12 * h)) ≠ 0 := by positivity
  rw [this, Real.log_mul (by norm_num) (mul_ne_zero h23 hprod),
    Real.log_mul h23 hprod, Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_prod hq]
  push_cast; ring

lemma log_W_le (h a : ℕ) (hh : 1 ≤ h) :
    Real.log (W h a) ≤ Real.log 4 + (Nat.log 2 h) * Real.log 2 +
      (Nat.log 3 (12 * h)) * Real.log 3 +
      (th 1 (T1 h a) + th 3 (T3 h a)) + (Qnp h).card * Real.log (4 * h) := by
  rw [log_W]
  rw [← Finset.sum_filter_add_sum_filter_not (FaSet h a) Nat.Prime]
  have e : ∑ q ∈ (FaSet h a).filter Nat.Prime, Real.log (q.minFac : ℝ)
      = ∑ q ∈ (FaSet h a).filter Nat.Prime, Real.log (q : ℝ) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [(Finset.mem_filter.mp hq).2.minFac_eq]
  rw [e]
  have := prime_part h a
  have := nonprime_part h a hh
  linarith

lemma log_Dden (h : ℕ) :
    Real.log (Dden h) = 2 * ∑ a ∈ Finset.range h, Real.log (W h a) := by
  have hpos : ∀ a : Fin h, (W h a : ℝ) ≠ 0 := fun a => by exact_mod_cast (W_pos h a).ne'
  have : (Dden h : ℝ) = (∏ a : Fin h, (W h a : ℝ)) ^ 2 := by unfold Dden; push_cast; rfl
  rw [this, Real.log_pow, Real.log_prod (fun a _ => hpos a)]
  rw [Fin.sum_univ_eq_sum_range (fun a => Real.log (W h a)) h]
  push_cast; ring

lemma log_Dden_le (h : ℕ) (hh : 1 ≤ h) :
    Real.log (Dden h) ≤ 2 * (h * (Real.log 4 + (Nat.log 2 h) * Real.log 2 +
      (Nat.log 3 (12 * h)) * Real.log 3 +
      (Qnp h).card * Real.log (4 * h))) +
      2 * ∑ a ∈ Finset.range h, (th 1 (T1 h a) + th 3 (T3 h a)) := by
  rw [log_Dden]
  have : ∑ a ∈ Finset.range h, Real.log (W h a) ≤
      ∑ a ∈ Finset.range h, ((Real.log 4 + (Nat.log 2 h) * Real.log 2 +
        (Nat.log 3 (12 * h)) * Real.log 3 +
        (Qnp h).card * Real.log (4 * h)) + (th 1 (T1 h a) + th 3 (T3 h a))) := by
    apply Finset.sum_le_sum
    intro a _
    have := log_W_le h a hh
    linarith
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  linarith

lemma sumT1_le (h : ℕ) (hh : 1 ≤ h) :
    ∑ a ∈ Finset.range h, (T1 h a : ℝ) ≤ 21 / 10 * (h : ℝ) ^ 2 + h := by
  have := sum_max_le 4 0 (by norm_num) (by norm_num) h (fun a => (T1 h a : ℝ)) (by
    intro a ha
    unfold T1
    rw [Nat.cast_max]
    apply max_le_max
    · push_cast; linarith
    · have : ((h - 1 - a : ℕ) : ℝ) + a + 1 = h := by exact_mod_cast (by omega : h - 1 - a + a + 1 = h)
      linarith)
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  nlinarith

lemma sumT3_le (h : ℕ) (hh : 1 ≤ h) :
    ∑ a ∈ Finset.range h, (T3 h a : ℝ) ≤ 37 / 42 * (h : ℝ) ^ 2 + h := by
  have := sum_max_le (4 / 3) 0 (by norm_num) (by norm_num) h (fun a => (T3 h a : ℝ)) (by
    intro a ha
    unfold T3
    rw [Nat.cast_max]
    apply max_le_max
    · have := Nat.cast_div_le (α := ℝ) (m := 4 * a) (n := 3)
      push_cast at this
      linarith
    · have : ((h - 1 - a : ℕ) : ℝ) + a + 1 = h := by exact_mod_cast (by omega : h - 1 - a + a + 1 = h)
      linarith)
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have e : ((h : ℝ) + (1 + 4 / 3) / 2 - 0) ^ 2 / (2 * (1 + 4 / 3)) + 4 / 3 * h * (h - 1) / 2 + 0 * h
      = 37 / 42 * (h : ℝ) ^ 2 - 1 / 6 * h + 7 / 24 := by ring
  linarith

lemma card_Qnp_le (h : ℕ) :
    (Qnp h).card ≤ (Nat.sqrt (4 * h) + 1) * (Nat.log 2 (4 * h) + 1) := by
  have hsub : Qnp h ⊆ ((Finset.range (Nat.sqrt (4 * h) + 1)) ×ˢ
      (Finset.range (Nat.log 2 (4 * h) + 1))).image (fun x : ℕ × ℕ => x.1 ^ x.2) := by
    intro q hq
    simp only [Qnp, Qset, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨⟨hq4, hpp, hodd, h3d⟩, hnp⟩ := hq
    obtain ⟨p, e, hp0, he, rfl⟩ := hpp
    have hp := hp0.nat_prime
    have he2 : 2 ≤ e := by
      by_contra hlt
      have : e = 1 := by omega
      subst this
      exact hnp (by simpa using hp)
    have hp2 : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos he2
    have hpe : p ^ e ≤ 4 * h := by omega
    refine Finset.mem_image.mpr ⟨(p, e), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_range]
    constructor
    · have : p * p ≤ 4 * h := by nlinarith
      have := Nat.le_sqrt.mpr this
      omega
    · have h2e : 2 ^ e ≤ 4 * h := (Nat.pow_le_pow_left hp.two_le e).trans hpe
      have := Nat.le_log_of_pow_le (by norm_num) h2e
      omega
  calc (Qnp h).card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = _ := by simp

/-- **Growth, modulo the Chebyshev-type bound.** -/
theorem growth_of_theta
    (hθ : ∀ j : ℕ, (j = 1 ∨ j = 3) → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, th j N ≤ (1 / 2 + ε) * N)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, Real.log (Dden h) ≤ (313 / 105 + ε) * (h : ℝ) ^ 2 := by
  have hε' : 0 < ε / 48 := by positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((hθ 1 (Or.inl rfl) _ hε').and (hθ 3 (Or.inr rfl) _ hε'))
  have tc : Tendsto (fun h : ℕ => (h : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ty : Tendsto (fun h : ℕ => Real.sqrt (4 * (h : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tc.const_mul_atTop (by norm_num))
  have ev1 : ∀ᶠ h : ℕ in atTop, 7 * N₀ + 4 ≤ 4 * h ∧ 1 ≤ h := by
    filter_upwards [eventually_ge_atTop (7 * N₀ + 4), eventually_ge_atTop 1] with h h1 h2
    exact ⟨by omega, h2⟩
  have evA : ∀ᶠ h : ℕ in atTop,
      2 + ε / 12 + 2 * Real.log 4 + 2 * Real.log 12 ≤ ε / 8 * h := by
    filter_upwards [tc.eventually_ge_atTop
      ((2 + ε / 12 + 2 * Real.log 4 + 2 * Real.log 12) / (ε / 8))] with h hh
    rw [div_le_iff₀ (by positivity)] at hh
    linarith
  have evB : ∀ᶠ h : ℕ in atTop, Real.log (h : ℝ) ≤ (ε / 16) * h :=
    tc.eventually (ev_log_le (by positivity))
  have evC : ∀ᶠ h : ℕ in atTop, (Real.log (Real.sqrt (4 * (h : ℝ))) ^ 2 ≤
      (ε / 1280) * Real.sqrt (4 * (h : ℝ)) ∧ 1 ≤ Real.log (Real.sqrt (4 * (h : ℝ)))) ∧
      1 ≤ Real.sqrt (4 * (h : ℝ)) :=
    ty.eventually (((ev_log_sq_le (by positivity)).and
      (Real.tendsto_log_atTop.eventually_ge_atTop 1)).and (eventually_ge_atTop 1))
  filter_upwards [ev1, evA, evB, evC] with h ⟨h7, h1⟩ hA hB ⟨⟨hC1, hC2⟩, hC3⟩
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast h1
  have hbase := log_Dden_le h h1
  -- the theta part
  have hsum : ∑ a ∈ Finset.range h, (th 1 (T1 h a) + th 3 (T3 h a)) ≤
      (1 / 2 + ε / 48) * (∑ a ∈ Finset.range h, (T1 h a : ℝ) + ∑ a ∈ Finset.range h, (T3 h a : ℝ)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have ha' := Finset.mem_range.mp ha
    have hT1 : N₀ ≤ T1 h a := by unfold T1; omega
    have hT3 : N₀ ≤ T3 h a := by unfold T3; omega
    have e1 := (hN₀ _ hT1).1
    have e2 := (hN₀ _ hT3).2
    linarith
  have hS1 := sumT1_le h h1
  have hS3 := sumT3_le h h1
  have key1 : 2 * ∑ a ∈ Finset.range h, (th 1 (T1 h a) + th 3 (T3 h a)) ≤
      2 * ((1 / 2 + ε / 48) * (313 / 105 * (h : ℝ) ^ 2 + 2 * h)) := by
    have : (∑ a ∈ Finset.range h, (T1 h a : ℝ) + ∑ a ∈ Finset.range h, (T3 h a : ℝ))
        ≤ 313 / 105 * (h : ℝ) ^ 2 + 2 * h := by linarith
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1 / 2 + ε / 48)
    linarith
  -- the card part
  set y := Real.sqrt (4 * (h : ℝ)) with hy
  have hy2 : y ^ 2 = 4 * h := Real.sq_sqrt (by positivity)
  have hN : (Nat.sqrt (4 * h) : ℝ) ≤ y := by
    have := Real.nat_sqrt_le_real_sqrt (a := 4 * h)
    have e : ((4 * h : ℕ) : ℝ) = 4 * (h : ℝ) := by push_cast; ring
    rw [e] at this
    exact this
  have hE : (Nat.log 2 (4 * h) : ℝ) ≤ 4 * Real.log y := by
    have h1 := Real.natLog_le_logb (4 * h) 2
    push_cast at h1
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hlx : Real.log (4 * (h : ℝ)) = 2 * Real.log y := by
      rw [← hy2, Real.log_pow]; norm_num
    have hlx0 : 0 ≤ Real.log (4 * (h : ℝ)) := Real.log_nonneg (by linarith)
    have : Real.logb 2 (4 * (h : ℝ)) ≤ 2 * Real.log (4 * (h : ℝ)) := by
      unfold Real.logb
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hcard : ((Qnp h).card : ℝ) ≤ 10 * y * Real.log y := by
    have := card_Qnp_le h
    have h2 : ((Qnp h).card : ℝ) ≤ ((Nat.sqrt (4 * h) : ℝ) + 1) * ((Nat.log 2 (4 * h) : ℝ) + 1) := by
      exact_mod_cast this
    have h3 : ((Nat.sqrt (4 * h) : ℝ) + 1) ≤ 2 * y := by linarith
    have h4 : ((Nat.log 2 (4 * h) : ℝ) + 1) ≤ 5 * Real.log y := by linarith
    calc _ ≤ _ := h2
      _ ≤ (2 * y) * (5 * Real.log y) := by
        apply mul_le_mul h3 h4 (by positivity) (by positivity)
      _ = _ := by ring
  have hlx : Real.log (4 * (h : ℝ)) = 2 * Real.log y := by
    rw [← hy2, Real.log_pow]; norm_num
  have f3 : 2 * ((Qnp h).card : ℝ) * Real.log (4 * h) ≤ ε / 8 * h := by
    rw [hlx]
    have hc0 : 0 ≤ (Qnp h).card := Nat.cast_nonneg _
    have : 2 * ((Qnp h).card : ℝ) * (2 * Real.log y) ≤ 2 * (10 * y * Real.log y) * (2 * Real.log y) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      linarith
    have h5 : y * Real.log y ^ 2 ≤ y * (ε / 1280 * y) := mul_le_mul_of_nonneg_left hC1 (by linarith)
    nlinarith
  have hL : (Nat.log 2 h : ℝ) * Real.log 2 ≤ Real.log h := by
    have : (2 : ℝ) ^ (Nat.log 2 h) ≤ h := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    calc (Nat.log 2 h : ℝ) * Real.log 2 = Real.log (2 ^ Nat.log 2 h) := by
          rw [Real.log_pow]
      _ ≤ Real.log h := Real.log_le_log (by positivity) this
  have hL3 : (Nat.log 3 (12 * h) : ℝ) * Real.log 3 ≤ Real.log 12 + Real.log h := by
    have : (3 : ℝ) ^ (Nat.log 3 (12 * h)) ≤ 12 * h := by
      exact_mod_cast Nat.pow_log_le_self 3 (by omega)
    calc (Nat.log 3 (12 * h) : ℝ) * Real.log 3 = Real.log (3 ^ Nat.log 3 (12 * h)) := by
          rw [Real.log_pow]
      _ ≤ Real.log (12 * h) := Real.log_le_log (by positivity) this
      _ = Real.log 12 + Real.log h := Real.log_mul (by norm_num) (by positivity)
  have f1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ h)
  have f2 := mul_le_mul_of_nonneg_left (hL.trans hB) (by linarith : (0 : ℝ) ≤ h)
  have hL3' : (Nat.log 3 (12 * h) : ℝ) * Real.log 3 ≤ Real.log 12 + ε / 16 * h := by linarith
  have f2' := mul_le_mul_of_nonneg_left hL3' (by linarith : (0 : ℝ) ≤ h)
  have f3' := mul_le_mul_of_nonneg_left f3 (by linarith : (0 : ℝ) ≤ h)
  nlinarith

end CatalanLambda.Mirror
