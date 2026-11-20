/-
The reciprocal-cutoff square-window proof is adapted from Tang,
dtq1997/li2-half-irrationality, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108,
Apache-2.0; see CatalanCore/Li2/Port/LICENSE and NOTICE. Other rows assemble
that port's existing theorems with the general rational-parameter content bounds.
-/
module

public import CatalanCore.Li2.Content.Local
public import CatalanCore.Li2.Content.Moments
public import CatalanCore.Li2.Content.Denominator
public import CatalanCore.Li2.Content.Difference
public import CatalanCore.Li2.Content.Numerator
public import CatalanCore.Li2.Content.Rate
public import CatalanCore.Li2.Content.MediumClosed
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P050
public import OAI.NumberTheory.Catalan.Polynomial.RationalProductFormula
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P036

@[expose] public section
set_option Elab.async false

/-! General rational-parameter content law, rows T1-T5. -/
open Polynomial Finset Filter
open scoped Topology BigOperators
open CatalanCore.Li2.Port
open CatalanCore.Li2.Port.Unified

namespace CatalanCore.Li2.Content

open Port.Unified.Proofs.Arithmetic

private theorem v_nonneg_draft (p : ℕ) (a : ℤ) : 0 ≤ v p a := by
  dsimp [v]
  rw [padicValRat.of_int]
  exact_mod_cast Nat.zero_le _

theorem Qtilde_GV_K (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (hb : 0 < b) (hab : IsCoprime a b) (ha : a ≠ 0) (hablt : |a| < b)
    {n : ℕ} (hn : 1 ≤ n) :
    Port.Li2.GV p (ParameterFamily.Qtilde (lam a b) n)
      (v p b * (Port.Li2.A2 n : ℚ) - v p a * (6 * (n : ℚ) ^ 2 + n) -
        v p (b - a) * S n - 4 * n * L p n) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hal : a < b := lt_of_le_of_lt (le_abs_self a) hablt
  have hba : b - a ≠ 0 := by omega
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  have habq : (a : ℚ) ≠ (b : ℚ) := by exact_mod_cast ne_of_lt hal
  have hz0 : lam a b ≠ 0 := div_ne_zero haq hbq
  have hz1 : lam a b ≠ 1 := by
    intro h
    exact habq ((div_eq_one_iff_eq hbq).mp h)
  rcases parameter_valuations p a b ha hb0 hba with ⟨hval, hinv, hratio⟩
  have hvg (r : ℚ) (h : r ≤ v p a - v p b) : Port.Li2.VG p (lam a b) r := by
    right
    rw [hval]
    exact h
  have hvgi (r : ℚ) (h : r ≤ v p b - v p a) : Port.Li2.VG p (lam a b)⁻¹ r := by
    right
    rw [hinv]
    exact h
  have hvgr (r : ℚ) (h : r ≤ v p a - v p (b-a)) :
      Port.Li2.VG p (lam a b / (1 - lam a b)) r := by
    right
    rw [hratio]
    exact h
  rcases prime_cases p a b hab ha hb0 hba with h | h | h | h
  · rcases h with ⟨_, _, _, hpb, hpba⟩
    have H := Qtilde_GV_num p (lam a b) (v p a) (v_nonneg_draft p a) hz0 hz1
      (hvgr 0 (by rw [hpba]; linarith [v_nonneg_draft p a]))
      (hvg 0 (by rw [hpb]; linarith [v_nonneg_draft p a]))
      (hvgi (-v p a) (by rw [hpb]; linarith)) hn
    simpa [hpb, hpba] using H
  · rcases h with ⟨_, _, _, hpa, hpba⟩
    have H := parameterQtilde_GV_den p (lam a b) (v p b) (v_nonneg_draft p b) hz0 hz1
      (hvgr 0 (by rw [hpa, hpba]; norm_num))
      (hvgi (v p b) (by rw [hpa]; linarith)) hn
    simpa [hpa, hpba] using H
  · rcases h with ⟨_, _, _, hpa, hpb⟩
    have H := Qtilde_GV_f p (lam a b) (v p (b-a)) (v_nonneg_draft p (b-a)) hz1
      (hvgr (-v p (b-a)) (by rw [hpa]; linarith))
      (hvg 0 (by rw [hpa, hpb]; norm_num))
      (hvgi 0 (by rw [hpa, hpb]; norm_num)) hn
    simpa [hpa, hpb] using H
  · rcases h with ⟨_, _, _, hpa, hpb, hpba⟩
    have H := Qtilde_GV_good_fallback p (lam a b) hz1
      (hvgr 0 (by rw [hpa, hpba]; norm_num))
      (hvg 0 (by rw [hpa, hpb]; norm_num))
      (hvgi 0 (by rw [hpa, hpb]; norm_num)) hn
    simpa [hpa, hpb, hpba, L] using H



noncomputable def term (z : ℚ) (n p : ℕ) : ℝ :=
  ((-padicValRat p (ParameterFamily.dtilde z n) : ℤ) : ℝ) * Real.log p
noncomputable def primes (lo hi : ℕ) : Finset ℕ :=
  (Finset.Ioc lo hi).filter Nat.Prime

theorem prime_partition (F : ℕ → ℝ) (E : Finset ℕ) (n k : ℕ)
    (hk : 4 ≤ k) (hkn : k ≤ n) (hE : ∀ p ∈ E, p.Prime ∧ p ≤ k) :
    (∑ p ∈ primes 0 (4 * n), F p) =
      (∑ p ∈ E, F p) + (∑ p ∈ (primes 0 4) \ E, F p) +
      (∑ p ∈ (primes 4 k) \ E, F p) +
      (∑ p ∈ primes k n, F p) + (∑ p ∈ primes n (4 * n), F p) := by
  classical
  let A := primes 0 4 \ E
  let B := primes 4 k \ E
  let C := primes k n
  let D := primes n (4*n)
  have bounds {lo hi p : ℕ} (hp : p ∈ primes lo hi) : lo < p ∧ p ≤ hi :=
    Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have hU : primes 0 (4*n) = (((E ∪ A) ∪ B) ∪ C) ∪ D := by
    ext p
    by_cases hmem : p ∈ E
    · have he := hE p hmem
      have hp0 := he.1.pos
      have hp4 : p ≤ 4*n := by omega
      simp [A, B, C, D, primes, hmem, he.1, hp0, hp4]
    · by_cases hpp : p.Prime
      · simp [A, B, C, D, primes, hmem, hpp] <;> omega
      · simp [A, B, C, D, primes, hmem, hpp]
  have d01 : Disjoint E A := Finset.disjoint_sdiff
  have d012 : Disjoint (E ∪ A) B := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_sdiff.mp hq).2 hp
    · have hp4 := (bounds (Finset.mem_sdiff.mp hp).1).2
      have hq4 := (bounds (Finset.mem_sdiff.mp hq).1).1
      omega
  have hp2 : ∀ p ∈ (E ∪ A) ∪ B, p ≤ k := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (hE p hp).2
      · have hp4 := (bounds (Finset.mem_sdiff.mp hp).1).2
        omega
    · exact (bounds (Finset.mem_sdiff.mp hp).1).2
  have d0123 : Disjoint ((E ∪ A) ∪ B) C := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := hp2 p hp
    have hq' := (bounds hq).1
    omega
  have hp3 : ∀ p ∈ ((E ∪ A) ∪ B) ∪ C, p ≤ n := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (hp2 p hp).trans hkn
    · exact (bounds hp).2
  have d01234 : Disjoint (((E ∪ A) ∪ B) ∪ C) D := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := hp3 p hp
    have hq' := (bounds hq).1
    omega
  rw [hU, Finset.sum_union d01234, Finset.sum_union d0123,
    Finset.sum_union d012, Finset.sum_union d01]



theorem exceptional_log_sum (a b : ℤ) (hb : 0 < b)
    (ha : a ≠ 0) (hba : b - a ≠ 0) :
    (∑ p ∈ exceptional a b,
      ((8 / 3 : ℝ) * (v p b : ℝ) - 6 * (v p a : ℝ) -
        (9 / 4 : ℝ) * (v p (b - a) : ℝ)) * Real.log p) =
      (8 / 3 : ℝ) * Real.log (b : ℝ) - 6 * Real.log |(a : ℝ)| -
        (9 / 4 : ℝ) * Real.log |((b - a : ℤ) : ℝ)| := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hp0 : a*b*(b-a) ≠ 0 := mul_ne_zero (mul_ne_zero ha hb0) hba
  have hpN : (a*b*(b-a)).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hp0
  have hpr : ∀ p ∈ exceptional a b, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hsub (x : ℤ) (hd : x ∣ a*b*(b-a)) :
      OAI.InternalCatalan.rationalPrimeSupport (x : ℚ) ⊆ exceptional a b := by
    have hdn : x.natAbs ∣ (a*b*(b-a)).natAbs := by
      rcases hd with ⟨k, hk⟩
      exact ⟨k.natAbs, by rw [hk, Int.natAbs_mul]⟩
    have hs := Nat.primeFactors_mono hdn hpN
    simpa [OAI.InternalCatalan.rationalPrimeSupport, exceptional] using hs
  have hformula (x : ℤ) (hx : x ≠ 0) (hd : x ∣ a*b*(b-a)) :
      Real.log |(x : ℝ)| = ∑ p ∈ exceptional a b, (v p x : ℝ) * Real.log p := by
    have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast hx
    have h := OAI.InternalCatalan.log_abs_rational_eq_sum_valuations_on
      (x : ℚ) hxq (exceptional a b) (hsub x hd) hpr
    simpa only [v, Rat.cast_intCast] using h
  have haF := hformula a ha ⟨b*(b-a), by ring⟩
  have hbF := hformula b hb0 ⟨a*(b-a), by ring⟩
  have hbaF := hformula (b-a) hba ⟨a*b, by ring⟩
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  rw [abs_of_pos hbR] at hbF
  rw [hbF, haF, hbaF]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring


open Port.Unified.Proofs.Arithmetic

private theorem parameterFactsDraft (a b : ℤ) (hb : 0 < b) (ha : a ≠ 0) (hablt : |a| < b) :
    lam a b ≠ 0 ∧ lam a b ≠ 1 ∧ |(lam a b : ℝ)| < 1 ∧ b-a ≠ 0 := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hal : a < b := lt_of_le_of_lt (le_abs_self a) hablt
  have habq : (a : ℚ) ≠ (b : ℚ) := by exact_mod_cast ne_of_lt hal
  refine ⟨div_ne_zero haq hbq, ?_, ?_, by omega⟩
  · intro h
    exact habq ((div_eq_one_iff_eq hbq).mp h)
  · have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
    have hR : |(a : ℝ)| < (b : ℝ) := by exact_mod_cast hablt
    dsimp [lam]
    push_cast
    rw [abs_div, abs_of_pos hbR]
    exact (div_lt_one hbR).mpr hR

private theorem notDvdAwayDraft (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hba : b-a ≠ 0) (hpE : p ∉ exceptional a b) :
    ¬ (p : ℤ) ∣ a*b*(b-a) := by
  intro hd
  have hn : (a*b*(b-a)).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha hb) hba)
  have hdN : p ∣ (a*b*(b-a)).natAbs := by
    rcases hd with ⟨k, hk⟩
    exact ⟨k.natAbs, by simp only [hk, Int.natAbs_mul, Int.natAbs_natCast]⟩
  exact hpE (Nat.mem_primeFactors.mpr ⟨Fact.out, hdN, hn⟩)

private noncomputable def fallbackCostDraft (n p : ℕ) : ℝ :=
  (-4 * (n : ℝ) * (Nat.log p (7*n-2) : ℝ)) * Real.log p

private theorem fallbackCostNonposDraft (n p : ℕ) (hp : p.Prime) :
    fallbackCostDraft n p ≤ 0 := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hNL : 0 ≤ (n : ℝ) * (Nat.log p (7*n-2) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hlog

private theorem genericFallbackDraft (a b : ℤ) (hb : 0 < b) (ha : a ≠ 0) (hablt : |a| < b)
    (n p : ℕ) (hn : 1 ≤ n) (hne : ParameterFamily.Qtilde (lam a b) n ≠ 0)
    (hp : p.Prime) (hpE : p ∉ exceptional a b) :
    fallbackCostDraft n p ≤ term (lam a b) n p := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, hz1, _, hba⟩ := parameterFactsDraft a b hb ha hablt
  obtain ⟨hz, hzi, hr, _⟩ := parameter_units p a b ha (ne_of_gt hb) hba
    (notDvdAwayDraft p a b ha (ne_of_gt hb) hba hpE)
  have hQ := Qtilde_GV_good_fallback p (lam a b) hz1 hr hz hzi hn
  have hv : (-4 * (n : ℝ) * (Nat.log p (7*n-2) : ℝ)) ≤
      ((-padicValRat p (ParameterFamily.dtilde (lam a b) n) : ℤ) : ℝ) := by
    exact_mod_cast parameter_dtilde_GV_lower (lam a b) n p hne hQ
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  exact mul_le_mul_of_nonneg_right hv hlog

private theorem tinyFallbackLimitDraft :
    Tendsto (fun n : ℕ => (∑ p ∈ primes 0 4, fallbackCostDraft n p) / (n : ℝ)^2)
      atTop (𝓝 0) := by
  have hp (p : ℕ) : Tendsto (fun n : ℕ => fallbackCostDraft n p / (n : ℝ)^2) atTop (𝓝 0) := by
    have h := (Port.Li2.PrimeSums.natLog_error_square_tendsto_zero p).neg.mul_const (Real.log p)
    simp only [neg_zero, zero_mul] at h
    convert h using 1
    funext n
    dsimp [fallbackCostDraft]
    ring
  have h := tendsto_finset_sum (primes 0 4) (fun p _ => hp p)
  simpa only [← Finset.sum_div, Finset.sum_const_zero] using h

private theorem tinyRangeDraft (a b : ℤ) (hb : 0 < b) (ha : a ≠ 0) (hablt : |a| < b)
    (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ParameterFamily.Qtilde (lam a b) n ≠ 0 →
      -e * (n : ℝ)^2 ≤ ∑ p ∈ (primes 0 4) \ exceptional a b, term (lam a b) n p := by
  have hmass : ∀ᶠ n : ℕ in atTop,
      -e ≤ (∑ p ∈ primes 0 4, fallbackCostDraft n p) / (n : ℝ)^2 :=
    Filter.Tendsto.eventually_const_le (by linarith) tinyFallbackLimitDraft
  filter_upwards [hmass, eventually_ge_atTop 1] with n hm hn
  intro hne
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc := (le_div_iff₀ (sq_pos_of_pos hnR)).mp hm
  have hdrop : (∑ p ∈ primes 0 4, fallbackCostDraft n p) ≤
      ∑ p ∈ (primes 0 4) \ exceptional a b, fallbackCostDraft n p :=
    Finset.sum_le_sum_of_subset_of_nonpos Finset.sdiff_subset
      (fun p hp _ => fallbackCostNonposDraft n p (Finset.mem_filter.mp hp).2)
  refine hc.trans (hdrop.trans (Finset.sum_le_sum ?_))
  intro p hp
  exact genericFallbackDraft a b hb ha hablt n p hn hne
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2 (Finset.mem_sdiff.mp hp).2

private theorem smallRangeDraft (a b : ℤ) (hb : 0 < b) (ha : a ≠ 0) (hablt : |a| < b)
    (δ e : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ParameterFamily.Qtilde (lam a b) n ≠ 0 →
      (-4*δ-e) * (n : ℝ)^2 ≤
        ∑ p ∈ (smallTailPrimes δ n) \ exceptional a b, term (lam a b) n p := by
  have hmass : ∀ᶠ n : ℕ in atTop,
      -4*δ-e ≤ smallTailFallbackBound δ n / (n : ℝ)^2 :=
    Filter.Tendsto.eventually_const_le (by linarith) (smallTailFallbackBound_tendsto δ hδ0 hδ1)
  filter_upwards [hmass, eventually_ge_atTop 1] with n hm hn
  intro hne
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc := (le_div_iff₀ (sq_pos_of_pos hnR)).mp hm
  have hdrop : smallTailFallbackBound δ n ≤
      ∑ p ∈ (smallTailPrimes δ n) \ exceptional a b, fallbackCostDraft n p :=
    Finset.sum_le_sum_of_subset_of_nonpos Finset.sdiff_subset
      (fun p hp _ => fallbackCostNonposDraft n p (Finset.mem_filter.mp hp).2)
  refine hc.trans (hdrop.trans (Finset.sum_le_sum ?_))
  intro p hp
  exact genericFallbackDraft a b hb ha hablt n p hn hne
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2 (Finset.mem_sdiff.mp hp).2


open Port.Unified.Proofs.Arithmetic
private theorem squareCutoffDraft (N n p : ℕ)
    (hn : 4 * (N + 1) ^ 2 ≤ n)
    (hp : ⌊((1:ℝ) / ((N:ℝ) + 1)) * (n:ℝ)⌋₊ < p) :
    4 * n < p * p := by
  have hd : (0:ℝ) < (N:ℝ) + 1 := by positivity
  have hnonneg : (0:ℝ) ≤ ((1:ℝ) / ((N:ℝ) + 1)) * (n:ℝ) := by positivity
  have hfloor : ((1:ℝ) / ((N:ℝ) + 1)) * (n:ℝ) < (p:ℝ) :=
    (Nat.floor_lt hnonneg).mp hp
  have hnp : (n:ℝ) < ((N:ℝ) + 1) * (p:ℝ) := by
    have hh : (n:ℝ) < (p:ℝ) * ((N:ℝ) + 1) :=
      (div_lt_iff₀ hd).mp (by
        simpa only [one_div, one_mul, div_eq_mul_inv, mul_comm] using! hfloor)
    nlinarith
  have hnR : (4:ℝ) * ((N:ℝ) + 1) ^ 2 ≤ (n:ℝ) := by
    exact_mod_cast hn
  have hp4 : (4:ℝ) * ((N:ℝ) + 1) < (p:ℝ) := by
    by_contra hh
    have hle : (p:ℝ) ≤ 4 * ((N:ℝ) + 1) := le_of_not_gt hh
    have hmul := mul_le_mul_of_nonneg_left hle hd.le
    nlinarith
  have hpp : (0:ℝ) < (p:ℝ) * ((p:ℝ) - 4 * ((N:ℝ) + 1)) := by
    apply mul_pos
    · linarith
    · linarith
  have hsq : (4:ℝ) * (n:ℝ) < (p:ℝ) ^ 2 := by
    nlinarith
  have hsqNat : 4 * n < p ^ 2 := by exact_mod_cast hsq
  simpa only [pow_two] using! hsqNat


theorem generic_ranges (a b : ℤ) (hb : 0 < b) (hab : IsCoprime a b)
    (ha : a ≠ 0) (hablt : |a| < b) (N : ℕ) (hN : 2 ≤ N) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ParameterFamily.Qtilde (lam a b) n ≠ 0 →
      let k := ⌊(n : ℝ) / ((N : ℝ) + 1)⌋₊
      (∀ p ∈ exceptional a b, p ≤ k) ∧
      (-e * (n : ℝ) ^ 2 ≤ ∑ p ∈ (primes 0 4) \ exceptional a b, term (lam a b) n p) ∧
      ((-4 / ((N : ℝ) + 1) - e) * (n : ℝ) ^ 2 ≤
        ∑ p ∈ (primes 4 k) \ exceptional a b, term (lam a b) n p) ∧
      ((mediumConst - e) * (n : ℝ) ^ 2 ≤
        ∑ p ∈ primes k n, term (lam a b) n p) ∧
      ((7 / 2 - e) * (n : ℝ) ^ 2 ≤ ∑ p ∈ primes n (4 * n), term (lam a b) n p) ∧
      (∀ p : ℕ, p.Prime → 4 * n < p → padicValRat p (ParameterFamily.dtilde (lam a b) n) ≤ 0) := by
  obtain ⟨hz0, hz1, habs, hba⟩ := parameterFactsDraft a b hb ha hablt
  let δ : ℝ := 1 / ((N : ℝ) + 1)
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_one (by positivity : 0 < (N : ℝ)+1)).mpr
    have h : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith
  have htiny := tinyRangeDraft a b hb ha hablt e he
  have hsmall := smallRangeDraft a b hb ha hablt δ e hδ0 hδ1 he
  have hmedium := parameter_mediumN_eventually_closed (lam a b) N hN e he
  have houter := parameter_outer_eventually_conditional (lam a b) e he
  have units (p : ℕ) (hp : p.Prime) (hpE : p ∉ exceptional a b) :
      (Port.Li2.VG p (lam a b) 0 ∧ Port.Li2.VG p (lam a b)⁻¹ 0 ∧
        Port.Li2.VG p (lam a b / (1 - lam a b)) 0 ∧
        ((lam a b ≠ 0 ∧ padicValRat p (lam a b) = 0) ∧
          (1-lam a b ≠ 0 ∧ padicValRat p (1-lam a b) = 0))) := by
    letI : Fact p.Prime := ⟨hp⟩
    exact parameter_units p a b ha (ne_of_gt hb) hba
      (notDvdAwayDraft p a b ha (ne_of_gt hb) hba hpE)
  let B : ℕ := (a*b*(b-a)).natAbs
  filter_upwards [htiny, hsmall, hmedium, houter,
    eventually_ge_atTop ((B+4)*(N+1)), eventually_ge_atTop (4*(N+1)^2),
    eventually_ge_atTop 4] with n ht hs hm ho hnBig hnSq hn4
  intro hne
  let k := ⌊(n : ℝ) / ((N : ℝ) + 1)⌋₊
  have hd : 0 < (N : ℝ)+1 := by positivity
  have hnon : 0 ≤ (n : ℝ) / ((N : ℝ)+1) := div_nonneg (Nat.cast_nonneg _) hd.le
  have hK : B+4 ≤ k := by
    apply (Nat.le_floor_iff hnon).mpr
    apply (le_div_iff₀ hd).mpr
    exact_mod_cast hnBig
  have hk4 : 4 ≤ k := by omega
  have hkn : k ≤ n := by
    have hF : (k : ℝ) ≤ (n : ℝ) / ((N : ℝ)+1) := Nat.floor_le hnon
    have hD : 1 ≤ (N : ℝ)+1 := by have h : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
    exact_mod_cast hF.trans (div_le_self (Nat.cast_nonneg n) hD)
  have hE : ∀ p ∈ exceptional a b, p ≤ k := by
    intro p hp
    have hpB : p ≤ B := Nat.le_of_mem_primeFactors hp
    omega
  have hfloor : ⌊(1 / ((N : ℝ)+1)) * (n : ℝ)⌋₊ = k := by
    dsimp [k]
    congr 1
    ring
  have hS : smallTailPrimes δ n = primes 4 k := by
    simp only [smallTailPrimes, primes, δ, hfloor]
  refine ⟨hE, ht hne, ?_, ?_, ?_, ?_⟩
  · have H := hs hne
    rw [hS] at H
    simpa only [δ, mul_one_div] using H
  · have hgram : ∀ p ∈ Finset.Ioc ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ n,
        ∀ hp : p.Prime,
          Port.Li2.GV p (ParameterFamily.binomGram (lam a b) n).det
            (Port.Unified.Stage0.HermitePreparation.normalizedDetLower n p) := by
      intro p hpI hp
      letI : Fact p.Prime := ⟨hp⟩
      have hpI' : k < p ∧ p ≤ n := by simpa only [hfloor] using Finset.mem_Ioc.mp hpI
      have hpE : p ∉ exceptional a b := by intro hpE; have h := hE p hpE; omega
      obtain ⟨_, _, _, hu⟩ := units p hp hpE
      exact Port.Unified.Stage0.HermitePreparation.actual_binomGram (lam a b) n p habs
        (by omega) hpI'.2 (squareCutoffDraft N n p hnSq (Finset.mem_Ioc.mp hpI).1) hu
    have H := hm (by omega : 0 < n) hne hgram
    simpa only [primes, Finset.sum_filter, term, hfloor, Nat.cast_add, Nat.cast_one] using H
  · have hout : ∀ p ∈ Finset.Ioc n (4*n), ∀ hp : p.Prime,
          Port.Li2.GV p (ParameterFamily.Qtilde (lam a b) n) (Port.Li2.outerPrimeBound p n) := by
      intro p hpI hp
      letI : Fact p.Prime := ⟨hp⟩
      have hpI' := Finset.mem_Ioc.mp hpI
      have hpE : p ∉ exceptional a b := by intro hpE; have h := hE p hpE; omega
      obtain ⟨hz, hzi, hr, _⟩ := units p hp hpE
      exact parameter_Qtilde_GV_outer p (by omega) (lam a b) hz1 hr hz hzi hpI'.1 hpI'.2
    have H := ho hne hout
    simpa only [primes, Finset.sum_filter, term] using H
  · intro p hp hpn
    letI : Fact p.Prime := ⟨hp⟩
    have hpE : p ∉ exceptional a b := by intro hpE; have h := hE p hpE; omega
    obtain ⟨hz, hzi, hr, _⟩ := units p hp hpE
    have H := parameter_dtilde_large_val_nonneg p (lam a b) hz1 hr hz hzi
      (by omega : 1 ≤ n) hpn hne
    omega


open Port.Unified.Proofs.Arithmetic

private noncomputable def exceptionalCostDraft (a b : ℤ) (n : ℕ) : ℝ :=
  ∑ p ∈ exceptional a b,
    ((v p b : ℝ) * (Port.Li2.A2 n : ℝ) - (v p a : ℝ) * (6*(n:ℝ)^2+n) -
      (v p (b-a) : ℝ) * (S n : ℝ) - 4*(n:ℝ)*(Nat.log p (7*n-2):ℝ)) * Real.log p

private theorem exceptionalLimitDraft (a b : ℤ) (hb : 0 < b) (ha : a ≠ 0) (hba : b-a ≠ 0) :
    Tendsto (fun n : ℕ => exceptionalCostDraft a b n / (n:ℝ)^2) atTop
      (𝓝 ((8/3:ℝ)*Real.log (b:ℝ)-6*Real.log |(a:ℝ)|-(9/4:ℝ)*Real.log |((b-a:ℤ):ℝ)|)) := by
  have hper (p : ℕ) : Tendsto (fun n : ℕ =>
      (((v p b : ℝ) * (Port.Li2.A2 n : ℝ) - (v p a : ℝ) * (6*(n:ℝ)^2+n) -
        (v p (b-a) : ℝ) * (S n : ℝ) - 4*(n:ℝ)*(Nat.log p (7*n-2):ℝ)) * Real.log p) / (n:ℝ)^2)
      atTop (𝓝 (((8/3:ℝ)*(v p b : ℝ)-6*(v p a : ℝ)-(9/4:ℝ)*(v p (b-a) : ℝ))*Real.log p)) := by
    have h := (((denominator_rate (v p b : ℝ)).add (numerator_rate (v p a : ℝ))).add
      (difference_rate (v p (b-a) : ℝ))).sub (Port.Li2.PrimeSums.natLog_error_square_tendsto_zero p)
    have hh := h.mul_const (Real.log p)
    convert hh using 1 <;> first | (funext n; ring) | ring
  have hsum := tendsto_finset_sum (exceptional a b) (fun p _ => hper p)
  rw [← exceptional_log_sum a b hb ha hba]
  simpa only [exceptionalCostDraft, ← Finset.sum_div] using hsum

private theorem exceptionalRangeDraft (a b : ℤ) (hb : 0 < b) (hab : IsCoprime a b)
    (ha : a ≠ 0) (hablt : |a| < b) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ParameterFamily.Qtilde (lam a b) n ≠ 0 →
      ((8/3:ℝ)*Real.log (b:ℝ)-6*Real.log |(a:ℝ)|-(9/4:ℝ)*Real.log |((b-a:ℤ):ℝ)|-e)*(n:ℝ)^2 ≤
        ∑ p ∈ exceptional a b, term (lam a b) n p := by
  obtain ⟨_, _, _, hba⟩ := parameterFactsDraft a b hb ha hablt
  have hmass : ∀ᶠ n : ℕ in atTop,
      (8/3:ℝ)*Real.log (b:ℝ)-6*Real.log |(a:ℝ)|-(9/4:ℝ)*Real.log |((b-a:ℤ):ℝ)|-e ≤
        exceptionalCostDraft a b n / (n:ℝ)^2 :=
    Filter.Tendsto.eventually_const_le (by linarith) (exceptionalLimitDraft a b hb ha hba)
  filter_upwards [hmass, eventually_ge_atTop 1] with n hm hn
  intro hne
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc := (le_div_iff₀ (sq_pos_of_pos hnR)).mp hm
  refine hc.trans (Finset.sum_le_sum ?_)
  intro p hp
  letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hvQ := parameter_dtilde_GV_lower (lam a b) n p hne
    (Qtilde_GV_K p a b hb hab ha hablt hn)
  have hv : ((v p b * (Port.Li2.A2 n : ℚ) - v p a * (6*(n:ℚ)^2+n) -
      v p (b-a) * S n - 4*n*L p n : ℚ) : ℝ) ≤
      ((-padicValRat p (ParameterFamily.dtilde (lam a b) n) : ℤ) : ℝ) := by exact_mod_cast hvQ
  dsimp [L] at hv
  push_cast at hv
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  simpa only [term, Int.cast_neg] using mul_le_mul_of_nonneg_right hv hlog


open Port.Unified.Proofs.Arithmetic

private theorem primeRangeEqDraft (K : ℕ) :
    (Finset.range (K+1)).filter Nat.Prime = primes 0 K := by
  ext p
  by_cases hp : p.Prime
  · have hp0 := hp.pos
    simp [primes, hp, hp0, Nat.lt_succ_iff]
  · simp [primes, hp]

theorem content_rate (a b : ℤ) (hb : 0 < b) (hab : IsCoprime a b)
    (ha : a ≠ 0) (hablt : |a| < b) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ParameterFamily.Qtilde (lam a b) n ≠ 0 →
      Real.log (ParameterFamily.dtilde (lam a b) n : ℝ) ≤
        -(CatalanCore.Li2.cRate a b - e) * (n : ℝ) ^ 2 := by
  obtain ⟨N, hN, _, _, hbudgetRaw⟩ := exists_finite_cutoff e he
  have hbudget : 4 / ((N : ℝ)+1) < e/2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hbudgetRaw
  have he10 : 0 < e/10 := by linarith
  have hgeneric := generic_ranges a b hb hab ha hablt N hN (e/10) he10
  have hexcept := exceptionalRangeDraft a b hb hab ha hablt (e/10) he10
  filter_upwards [hgeneric, hexcept, eventually_ge_atTop (4*(N+1)),
    eventually_ge_atTop 1] with n hg hx hnCut hn1
  intro hne
  let k := ⌊(n : ℝ) / ((N : ℝ)+1)⌋₊
  obtain ⟨hE, htiny, hsmall, hmedium, houter, hlarge⟩ := hg hne
  have hExc := hx hne
  have hd : 0 < (N : ℝ)+1 := by positivity
  have hnon : 0 ≤ (n : ℝ) / ((N : ℝ)+1) := div_nonneg (Nat.cast_nonneg _) hd.le
  have hk4 : 4 ≤ k := by
    apply (Nat.le_floor_iff hnon).mpr
    apply (le_div_iff₀ hd).mpr
    exact_mod_cast hnCut
  have hkn : k ≤ n := by
    have hF : (k : ℝ) ≤ (n : ℝ) / ((N : ℝ)+1) := Nat.floor_le hnon
    have hD : 1 ≤ (N : ℝ)+1 := by have h : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
    exact_mod_cast hF.trans (div_le_self (Nat.cast_nonneg n) hD)
  have hpart := prime_partition (term (lam a b) n) (exceptional a b) n k hk4 hkn
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hE p hp⟩)
  dsimp only [k] at hpart
  have hlog := parameter_log_dtilde_le_neg_prime_range (lam a b) n (4*n)
    (fun p hp hpn => by exact_mod_cast hlarge p hp hpn)
  rw [primeRangeEqDraft] at hlog
  change Real.log (ParameterFamily.dtilde (lam a b) n : ℝ) ≤
    -(∑ p ∈ primes 0 (4*n), term (lam a b) n p) at hlog
  have hbudgetMul : (4 / ((N : ℝ)+1)) * (n : ℝ)^2 ≤ (e/2) * (n : ℝ)^2 :=
    mul_le_mul_of_nonneg_right hbudget.le (sq_nonneg _)
  have hsum : (CatalanCore.Li2.cRate a b - e) * (n : ℝ)^2 ≤
      ∑ p ∈ primes 0 (4*n), term (lam a b) n p := by
    rw [hpart]
    have hall := add_le_add (add_le_add (add_le_add (add_le_add hExc htiny) hsmall) hmedium) houter
    refine (le_add_of_nonneg_right (sub_nonneg.mpr hbudgetMul)).trans ?_
    convert hall using 1 <;> (unfold CatalanCore.Li2.cRate mediumConst; ring)
  calc
    Real.log (ParameterFamily.dtilde (lam a b) n : ℝ) ≤
        -(∑ p ∈ primes 0 (4*n), term (lam a b) n p) := hlog
    _ ≤ -((CatalanCore.Li2.cRate a b - e) * (n : ℝ)^2) := neg_le_neg hsum
    _ = -(CatalanCore.Li2.cRate a b - e) * (n : ℝ)^2 := by ring


end CatalanCore.Li2.Content

#print axioms CatalanCore.Li2.Content.Qtilde_GV_K
#print axioms CatalanCore.Li2.Content.prime_partition
#print axioms CatalanCore.Li2.Content.exceptional_log_sum
#print axioms CatalanCore.Li2.Content.generic_ranges
#print axioms CatalanCore.Li2.Content.content_rate
