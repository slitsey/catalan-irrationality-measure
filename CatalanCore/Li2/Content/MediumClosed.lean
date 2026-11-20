module

public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P039
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

@[expose] public section

/-!
Closed form of the medium-prime profile integral.

Tang's port bounds the medium primes `⌊n/(N+1)⌋ < p ≤ n` below by the finite cell sum
`∑_{A=1}^{N} cellIntegral A` (times `n²`).  Partial fractions turn `cellIntegral A` into
`-(7/2)(1/A+1/(A+1)) + 16/(4A+1) + 16/(4A+3) + 4/(2A+1) - (9/2)/(3A+1) - (9/2)/(3A+2)`,
so the partial sums are explicit harmonic-number combinations and converge (from above, the
cells being negative) to `28 log 2 - (9/2) log 3 - 181/12`.
-/

namespace CatalanCore.Li2.Content

open CatalanCore.Li2.Port.Unified
open CatalanCore.Li2.Port.Unified.Stage0.HermitePreparation
open CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
open Filter Topology Finset

/-- The medium-prime constant: the integral of the profile over `(0,1]`. -/
noncomputable def mediumConst : ℝ := 28 * Real.log 2 - 9 / 2 * Real.log 3 - 181 / 12

theorem cellIntegral_partial_fractions (A : ℝ) (hA : 1 ≤ A) :
    cellIntegral A =
      -(7 / 2) * (1 / A + 1 / (A + 1)) + 16 / (4 * A + 1) + 16 / (4 * A + 3) +
        4 / (2 * A + 1) - (9 / 2) / (3 * A + 1) - (9 / 2) / (3 * A + 2) := by
  have h0 : 0 < A := by linarith
  unfold cellIntegral
  field_simp
  ring

theorem cellIntegral_nonpos (A : ℝ) (hA : 1 ≤ A) : cellIntegral A ≤ 0 := by
  have h0 : 0 < A := by linarith
  unfold cellIntegral
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)

/-- Harmonic closed form of the partial sums, indexed by `M = N + 1`. -/
noncomputable def cellClosed (M : ℕ) : ℝ :=
  16 * (harmonic (4 * M) : ℝ) - 4 * (harmonic (2 * M) : ℝ) - 9 / 2 * (harmonic (3 * M) : ℝ) -
    15 / 2 * (harmonic M : ℝ) + 7 / (2 * (M : ℝ)) - 181 / 12

private theorem harm4 (n : ℕ) : (harmonic (n + 4) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) +
    1 / ((n : ℝ) + 2) + 1 / ((n : ℝ) + 3) + 1 / ((n : ℝ) + 4) := by
  have e : n + 4 = n + 1 + 1 + 1 + 1 := by omega
  rw [e, harmonic_succ, harmonic_succ, harmonic_succ, harmonic_succ]
  push_cast
  ring

private theorem harm3 (n : ℕ) : (harmonic (n + 3) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) +
    1 / ((n : ℝ) + 2) + 1 / ((n : ℝ) + 3) := by
  have e : n + 3 = n + 1 + 1 + 1 := by omega
  rw [e, harmonic_succ, harmonic_succ, harmonic_succ]
  push_cast
  ring

private theorem harm2 (n : ℕ) : (harmonic (n + 2) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) +
    1 / ((n : ℝ) + 2) := by
  have e : n + 2 = n + 1 + 1 := by omega
  rw [e, harmonic_succ, harmonic_succ]
  push_cast
  ring

private theorem harm1 (n : ℕ) : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
  rw [harmonic_succ]
  push_cast
  ring

theorem cellClosed_step (N : ℕ) :
    cellClosed (N + 2) - cellClosed (N + 1) = cellIntegral ((N : ℝ) + 1) := by
  have hA : (1 : ℝ) ≤ (N : ℝ) + 1 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
  rw [cellIntegral_partial_fractions _ hA]
  have e4 : 4 * (N + 2) = 4 * (N + 1) + 4 := by ring
  have e3 : 3 * (N + 2) = 3 * (N + 1) + 3 := by ring
  have e2 : 2 * (N + 2) = 2 * (N + 1) + 2 := by ring
  unfold cellClosed
  rw [e4, e3, e2, harm4, harm3, harm2, show N + 2 = (N + 1) + 1 from rfl, harm1]
  push_cast
  have h0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  field_simp
  ring

theorem cellSum_eq_closed (N : ℕ) :
    (∑ A ∈ Finset.Ico (1 : ℕ) (N + 1), cellIntegral (A : ℝ)) = cellClosed (N + 1) := by
  induction N with
  | zero =>
    simp [cellClosed, harmonic, Finset.sum_range_succ]
    norm_num
  | succ N ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ N + 1), ih]
    have := cellClosed_step N
    push_cast at this ⊢
    linarith

private theorem tendsto_harm_mul (k : ℕ) (hk : 0 < k) :
    Tendsto (fun M : ℕ => (harmonic (k * M) : ℝ) - Real.log ((k : ℝ) * M)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
  have h := Real.tendsto_harmonic_sub_log
  have hk' : Tendsto (fun M : ℕ => k * M) atTop atTop :=
    Filter.tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_left M hk) tendsto_id
  have := h.comp hk'
  simpa [Function.comp_def] using this

theorem cellClosed_tendsto :
    Tendsto cellClosed atTop (𝓝 mediumConst) := by
  have h4 := tendsto_harm_mul 4 (by norm_num)
  have h2 := tendsto_harm_mul 2 (by norm_num)
  have h3 := tendsto_harm_mul 3 (by norm_num)
  have h1 := tendsto_harm_mul 1 (by norm_num)
  have hz : Tendsto (fun M : ℕ => (7 / 2 : ℝ) / (M : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hcomb := ((((h4.const_mul 16).sub (h2.const_mul 4)).sub (h3.const_mul (9 / 2))).sub
    (h1.const_mul (15 / 2))).add hz
  have hlim := hcomb.add_const (28 * Real.log 2 - 9 / 2 * Real.log 3 - 181 / 12)
  have hg : (16 * Real.eulerMascheroniConstant - 4 * Real.eulerMascheroniConstant -
      9 / 2 * Real.eulerMascheroniConstant - 15 / 2 * Real.eulerMascheroniConstant + 0 +
      (28 * Real.log 2 - 9 / 2 * Real.log 3 - 181 / 12)) = mediumConst := by
    unfold mediumConst; ring
  rw [hg] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hl4 : Real.log (4 * (M : ℝ)) = 2 * Real.log 2 + Real.log M := by
    rw [Real.log_mul (by norm_num) hMpos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    norm_num
  have hl2 : Real.log (2 * (M : ℝ)) = Real.log 2 + Real.log M :=
    Real.log_mul (by norm_num) hMpos.ne'
  have hl3 : Real.log (3 * (M : ℝ)) = Real.log 3 + Real.log M :=
    Real.log_mul (by norm_num) hMpos.ne'
  unfold cellClosed
  simp only [Nat.cast_ofNat, Nat.cast_one, one_mul, hl4, hl2, hl3, one_mul] at *
  push_cast
  ring_nf

theorem cellSum_ge_mediumConst (N : ℕ) :
    mediumConst ≤ ∑ A ∈ Finset.Ico (1 : ℕ) (N + 1), cellIntegral (A : ℝ) := by
  have hanti : Antitone (fun N : ℕ => ∑ A ∈ Finset.Ico (1 : ℕ) (N + 1), cellIntegral (A : ℝ)) := by
    apply antitone_nat_of_succ_le
    intro N
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ N + 1)]
    have : cellIntegral ((N + 1 : ℕ) : ℝ) ≤ 0 :=
      cellIntegral_nonpos _ (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; push_cast; linarith)
    linarith
  have ht : Tendsto (fun N : ℕ => ∑ A ∈ Finset.Ico (1 : ℕ) (N + 1), cellIntegral (A : ℝ)) atTop
      (𝓝 mediumConst) := by
    simp only [cellSum_eq_closed]
    exact cellClosed_tendsto.comp (tendsto_add_atTop_nat 1)
  exact hanti.le_of_tendsto ht N

theorem profileWindowClosedSumN_eventually_lower_closed (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (mediumConst - ε) * (n : ℝ) ^ 2 ≤ profileWindowClosedSumN N n := by
  have hmass : ∀ᶠ n : ℕ in atTop, mediumConst - ε ≤ profileWindowClosedSumN N n / (n : ℝ) ^ 2 :=
    Filter.Tendsto.eventually_const_le (by
      have := cellSum_ge_mediumConst N
      linarith) (profileWindowClosedSumN_tendsto N)
  filter_upwards [hmass, eventually_ge_atTop (1 : ℕ)] with n hmassn hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  exact (le_div_iff₀ (sq_pos_of_pos hnpos)).mp hmassn

/-- The medium-prime lower bound with the closed-form constant (replaces `-523/840 + (2/3)/(N+1)²`). -/
theorem parameter_mediumN_eventually_closed (lam : ℚ) (N : ℕ) (hN : 2 ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 0 < n → ParameterFamily.Qtilde lam n ≠ 0 →
      (∀ p ∈ Finset.Ioc ⌊((1 : ℝ) / ((N : ℝ) + 1)) * (n : ℝ)⌋₊ n,
        ∀ hp : p.Prime,
          letI : Fact p.Prime := ⟨hp⟩
          CatalanCore.Li2.Port.Li2.GV p (ParameterFamily.binomGram lam n).det
            (normalizedDetLower n p)) →
      (mediumConst - ε) * (n : ℝ) ^ 2 ≤
        ∑ p ∈ Finset.Ioc ⌊((1 : ℝ) / ((N : ℝ) + 1)) * (n : ℝ)⌋₊ n,
          if p.Prime then
            ((-padicValRat p (ParameterFamily.dtilde lam n) : ℤ) : ℝ) * Real.log (p : ℝ)
          else 0 := by
  filter_upwards [profileWindowClosedSumN_eventually_lower_closed N ε hε] with n hprofile
  intro hn hne hgram
  exact hprofile.trans
    (parameter_profileWindowClosedSumN_le_valuation lam N n (by omega : 1 ≤ N) hn hne hgram)

end CatalanCore.Li2.Content

#print axioms CatalanCore.Li2.Content.cellClosed_tendsto
#print axioms CatalanCore.Li2.Content.cellSum_ge_mediumConst
#print axioms CatalanCore.Li2.Content.parameter_mediumN_eventually_closed
