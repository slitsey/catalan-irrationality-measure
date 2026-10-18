import CatalanLambda.Integrality
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt

/-!
# Growth of `log D_h`: reduction to a Chebyshev-type upper bound for `θ(x; 4, a)`
-/

open Finset Classical Filter

namespace CatalanLambda

/-- `θ(N; 4, j) = ∑_{n ≤ N, n prime, n ≡ j (4)} log n`. -/
noncomputable def th (j N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n.Prime ∧ n % 4 = j), Real.log n

lemma th_nonneg (j N : ℕ) : 0 ≤ th j N :=
  Finset.sum_nonneg fun n hn => by
    have := (Finset.mem_filter.mp hn).2.1.one_lt
    exact Real.log_nonneg (by exact_mod_cast this.le)

/-- thresholds -/
def T1 (h a : ℕ) : ℕ := max (4 * a + 2) (h - 1 - a)
def T3 (h a : ℕ) : ℕ := max ((4 * a + 2) / 3) (h - 1 - a)

/-- the set of active odd prime powers at `a` -/
noncomputable def Fa (h a : ℕ) : Finset ℕ := (Qset h).filter (fun q => uq h q a)

lemma prime_part (h a : ℕ) :
    ∑ q ∈ (Fa h a).filter Nat.Prime, Real.log q ≤ th 3 (T1 h a) + th 1 (T3 h a) := by
  set S3 := (Finset.range (T1 h a + 1)).filter (fun n => n.Prime ∧ n % 4 = 3)
  set S1 := (Finset.range (T3 h a + 1)).filter (fun n => n.Prime ∧ n % 4 = 1)
  have hdisj : Disjoint S3 S1 := by
    rw [Finset.disjoint_left]
    intro n h3 h1
    have := (Finset.mem_filter.mp h3).2.2
    have := (Finset.mem_filter.mp h1).2.2
    omega
  have hsub : (Fa h a).filter Nat.Prime ⊆ S3 ∪ S1 := by
    intro q hq
    simp only [Fa, Qset, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨⟨⟨hq4, hpp, hodd⟩, hu⟩, hqp⟩ := hq
    have hq2 : q % 2 = 1 := Nat.odd_iff.mp hodd
    simp only [Finset.mem_union, S3, S1, Finset.mem_filter, Finset.mem_range]
    by_cases h3 : q % 4 = 3
    · left
      have hj : jq q = 1 := by simp [jq, h3]
      unfold uq kq at hu
      rw [hj] at hu
      unfold T1
      refine ⟨by omega, hqp, h3⟩
    · right
      have h1 : q % 4 = 1 := by omega
      have hj : jq q = 3 := by simp [jq, h3]
      unfold uq kq at hu
      rw [hj] at hu
      unfold T3
      refine ⟨by omega, hqp, h1⟩
  calc ∑ q ∈ (Fa h a).filter Nat.Prime, Real.log q
      ≤ ∑ q ∈ S3 ∪ S1, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n hn _
        rcases Finset.mem_union.mp hn with h | h <;>
          exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp h).2.1.one_lt.le)
    _ = th 3 (T1 h a) + th 1 (T3 h a) := by
        rw [Finset.sum_union hdisj]; rfl

/-- non-prime odd prime powers `≤ 4h` -/
noncomputable def Qnp (h : ℕ) : Finset ℕ := (Qset h).filter (fun q => ¬ q.Prime)

lemma nonprime_part (h a : ℕ) (hh : 1 ≤ h) :
    ∑ q ∈ (Fa h a).filter (fun q => ¬ q.Prime), Real.log (q.minFac : ℝ)
      ≤ (Qnp h).card * Real.log (4 * h) := by
  have h4 : (1 : ℝ) ≤ 4 * h := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  calc ∑ q ∈ (Fa h a).filter (fun q => ¬ q.Prime), Real.log (q.minFac : ℝ)
      ≤ ∑ q ∈ (Fa h a).filter (fun q => ¬ q.Prime), Real.log (4 * h : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        simp only [Fa, Qset, Finset.mem_filter, Finset.mem_range] at hq
        obtain ⟨⟨⟨hq4, hpp, hodd⟩, hu⟩, hqp⟩ := hq
        have hqpos : 0 < q := hpp.pos
        have : q.minFac ≤ q := Nat.minFac_le hqpos
        apply Real.log_le_log (by exact_mod_cast Nat.minFac_pos q)
        have : (q.minFac : ℝ) ≤ (4 * h : ℕ) := by exact_mod_cast (by omega : q.minFac ≤ 4 * h)
        simpa using this
    _ ≤ ∑ q ∈ Qnp h, Real.log (4 * h : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          simp only [Fa, Qnp, Finset.mem_filter] at hq ⊢
          exact ⟨hq.1.1, hq.2⟩
        · intros; exact Real.log_nonneg h4
    _ = (Qnp h).card * Real.log (4 * h) := by
        rw [Finset.sum_const, nsmul_eq_mul]

lemma log_W (h a : ℕ) :
    Real.log (W h a) = Real.log 4 + (Nat.log 2 h) * Real.log 2 +
      ∑ q ∈ Fa h a, Real.log (q.minFac : ℝ) := by
  have hq : ∀ q ∈ Fa h a, (q.minFac : ℝ) ≠ 0 := fun q _ => by
    exact_mod_cast (Nat.minFac_pos q).ne'
  have : (W h a : ℝ) = 4 * (2 ^ Nat.log 2 h * ∏ q ∈ Fa h a, (q.minFac : ℝ)) := by
    unfold W Wm Wodd Fa
    push_cast
    rfl
  have hprod : (∏ q ∈ Fa h a, (q.minFac : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hq
  rw [this, Real.log_mul (by norm_num) (mul_ne_zero (by positivity) hprod),
    Real.log_mul (by positivity) hprod, Real.log_pow, Real.log_prod hq]
  push_cast; ring

lemma log_W_le (h a : ℕ) (hh : 1 ≤ h) :
    Real.log (W h a) ≤ Real.log 4 + (Nat.log 2 h) * Real.log 2 +
      (th 3 (T1 h a) + th 1 (T3 h a)) + (Qnp h).card * Real.log (4 * h) := by
  rw [log_W]
  rw [← Finset.sum_filter_add_sum_filter_not (Fa h a) Nat.Prime]
  have e : ∑ q ∈ (Fa h a).filter Nat.Prime, Real.log (q.minFac : ℝ)
      = ∑ q ∈ (Fa h a).filter Nat.Prime, Real.log (q : ℝ) := by
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
      (Qnp h).card * Real.log (4 * h))) +
      2 * ∑ a ∈ Finset.range h, (th 3 (T1 h a) + th 1 (T3 h a)) := by
  rw [log_Dden]
  have : ∑ a ∈ Finset.range h, Real.log (W h a) ≤
      ∑ a ∈ Finset.range h, ((Real.log 4 + (Nat.log 2 h) * Real.log 2 +
        (Qnp h).card * Real.log (4 * h)) + (th 3 (T1 h a) + th 1 (T3 h a))) := by
    apply Finset.sum_le_sum
    intro a _
    have := log_W_le h a hh
    linarith
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
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

lemma sumT1_le (h : ℕ) (hh : 1 ≤ h) :
    ∑ a ∈ Finset.range h, (T1 h a : ℝ) ≤ 21 / 10 * (h : ℝ) ^ 2 + h := by
  have := sum_max_le 4 2 (by norm_num) (by norm_num) h (fun a => (T1 h a : ℝ)) (by
    intro a ha
    unfold T1
    rw [Nat.cast_max]
    apply max_le_max
    · push_cast; exact le_rfl
    · have : ((h - 1 - a : ℕ) : ℝ) + a + 1 = h := by exact_mod_cast (by omega : h - 1 - a + a + 1 = h)
      linarith)
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  nlinarith

lemma sumT3_le (h : ℕ) (hh : 1 ≤ h) :
    ∑ a ∈ Finset.range h, (T3 h a : ℝ) ≤ 37 / 42 * (h : ℝ) ^ 2 + h := by
  have := sum_max_le (4 / 3) (2 / 3) (by norm_num) (by norm_num) h (fun a => (T3 h a : ℝ)) (by
    intro a ha
    unfold T3
    rw [Nat.cast_max]
    apply max_le_max
    · have := Nat.cast_div_le (α := ℝ) (m := 4 * a + 2) (n := 3)
      push_cast at this
      linarith
    · have : ((h - 1 - a : ℕ) : ℝ) + a + 1 = h := by exact_mod_cast (by omega : h - 1 - a + a + 1 = h)
      linarith)
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have e : ((h : ℝ) + (1 + 4 / 3) / 2 - 2 / 3) ^ 2 / (2 * (1 + 4 / 3)) + 4 / 3 * h * (h - 1) / 2 + 2 / 3 * h = 37 / 42 * (h : ℝ) ^ 2 + 3 / 14 * h + 3 / 56 := by ring
  linarith

lemma card_Qnp_le (h : ℕ) :
    (Qnp h).card ≤ (Nat.sqrt (4 * h) + 1) * (Nat.log 2 (4 * h) + 1) := by
  have hsub : Qnp h ⊆ ((Finset.range (Nat.sqrt (4 * h) + 1)) ×ˢ
      (Finset.range (Nat.log 2 (4 * h) + 1))).image (fun x : ℕ × ℕ => x.1 ^ x.2) := by
    intro q hq
    simp only [Qnp, Qset, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨⟨hq4, hpp, hodd⟩, hnp⟩ := hq
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

/-- **Growth, modulo the Chebyshev-type bound.** -/
theorem growth_of_theta
    (hθ : ∀ j : ℕ, (j = 1 ∨ j = 3) → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, th j N ≤ (1 / 2 + ε) * N)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, Real.log (Dden h) ≤ (313 / 105 + ε) * (h : ℝ) ^ 2 := by
  have hε' : 0 < ε / 24 := by positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((hθ 3 (Or.inr rfl) _ hε').and (hθ 1 (Or.inl rfl) _ hε'))
  have tc : Tendsto (fun h : ℕ => (h : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ty : Tendsto (fun h : ℕ => Real.sqrt (4 * (h : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tc.const_mul_atTop (by norm_num))
  have ev1 : ∀ᶠ h : ℕ in atTop, 7 * N₀ + 4 ≤ 4 * h ∧ 1 ≤ h := by
    filter_upwards [eventually_ge_atTop (7 * N₀ + 4), eventually_ge_atTop 1] with h h1 h2
    exact ⟨by omega, h2⟩
  have evA : ∀ᶠ h : ℕ in atTop, 2 + ε / 6 + 2 * Real.log 4 ≤ ε / 4 * h := by
    filter_upwards [tc.eventually_ge_atTop ((2 + ε / 6 + 2 * Real.log 4) / (ε / 4))] with h hh
    rw [div_le_iff₀ (by positivity)] at hh
    linarith
  have evB : ∀ᶠ h : ℕ in atTop, Real.log (h : ℝ) ≤ (ε / 8) * h :=
    tc.eventually (ev_log_le (by positivity))
  have evC : ∀ᶠ h : ℕ in atTop, (Real.log (Real.sqrt (4 * (h : ℝ))) ^ 2 ≤
      (ε / 640) * Real.sqrt (4 * (h : ℝ)) ∧ 1 ≤ Real.log (Real.sqrt (4 * (h : ℝ)))) ∧
      1 ≤ Real.sqrt (4 * (h : ℝ)) :=
    ty.eventually (((ev_log_sq_le (by positivity)).and
      (Real.tendsto_log_atTop.eventually_ge_atTop 1)).and (eventually_ge_atTop 1))
  filter_upwards [ev1, evA, evB, evC] with h ⟨h7, h1⟩ hA hB ⟨⟨hC1, hC2⟩, hC3⟩
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast h1
  have hbase := log_Dden_le h h1
  -- the theta part
  have hsum : ∑ a ∈ Finset.range h, (th 3 (T1 h a) + th 1 (T3 h a)) ≤
      (1 / 2 + ε / 24) * (∑ a ∈ Finset.range h, (T1 h a : ℝ) + ∑ a ∈ Finset.range h, (T3 h a : ℝ)) := by
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
  have key1 : 2 * ∑ a ∈ Finset.range h, (th 3 (T1 h a) + th 1 (T3 h a)) ≤
      2 * ((1 / 2 + ε / 24) * (313 / 105 * (h : ℝ) ^ 2 + 2 * h)) := by
    have : (∑ a ∈ Finset.range h, (T1 h a : ℝ) + ∑ a ∈ Finset.range h, (T3 h a : ℝ))
        ≤ 313 / 105 * (h : ℝ) ^ 2 + 2 * h := by linarith
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1 / 2 + ε / 24)
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
  have f3 : 2 * ((Qnp h).card : ℝ) * Real.log (4 * h) ≤ ε / 4 * h := by
    rw [hlx]
    have hc0 : 0 ≤ (Qnp h).card := Nat.cast_nonneg _
    have : 2 * ((Qnp h).card : ℝ) * (2 * Real.log y) ≤ 2 * (10 * y * Real.log y) * (2 * Real.log y) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      linarith
    have h5 : y * Real.log y ^ 2 ≤ y * (ε / 640 * y) := mul_le_mul_of_nonneg_left hC1 (by linarith)
    nlinarith
  have hL : (Nat.log 2 h : ℝ) * Real.log 2 ≤ Real.log h := by
    have : (2 : ℝ) ^ (Nat.log 2 h) ≤ h := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    calc (Nat.log 2 h : ℝ) * Real.log 2 = Real.log (2 ^ Nat.log 2 h) := by
          rw [Real.log_pow]
      _ ≤ Real.log h := Real.log_le_log (by positivity) this
  have f1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ h)
  have f2 := mul_le_mul_of_nonneg_left (hL.trans hB) (by linarith : (0 : ℝ) ≤ h)
  have f3' := mul_le_mul_of_nonneg_left f3 (by linarith : (0 : ℝ) ≤ h)
  nlinarith

end CatalanLambda
