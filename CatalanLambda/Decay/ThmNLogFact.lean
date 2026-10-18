module

public import CatalanLambda.Decay.ThmNNodes
public import Mathlib.Analysis.SumIntegralComparisons

@[expose] public section

/-!
# Theorem N_ρ, stage 3b: [R2], the energy of the uniform grid `{b/h}`
-/

open Finset MeasureTheory intervalIntegral

namespace CatalanLambda.Decay

/-- Upper Stirling-type bound `log n! ≤ 1 + ½ log n + n log n - n`. -/
lemma log_factorial_le (n : ℕ) :
    Real.log (n.factorial) ≤ 1 + (1 / 2) * Real.log n + n * Real.log n - n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 := Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
    simp only [Function.comp, Nat.succ_eq_add_one, zero_add] at h1
    have e1 := Stirling.log_stirlingSeq_formula (m + 1)
    have e0 := Stirling.log_stirlingSeq_formula 1
    rw [Stirling.stirlingSeq_one] at e0
    have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have l0 : Real.log (Real.exp 1 / Real.sqrt 2) = 1 - (1 / 2) * Real.log 2 := by
      rw [Real.log_div (Real.exp_pos 1).ne' hs2.ne', Real.log_exp, Real.log_sqrt (by norm_num)]; ring
    have l1 : Real.log (2 * ((m + 1 : ℕ) : ℝ)) = Real.log 2 + Real.log ((m + 1 : ℕ) : ℝ) := by
      rw [Real.log_mul (by norm_num) hm.ne']
    have l2 : Real.log (((m + 1 : ℕ) : ℝ) / Real.exp 1) = Real.log ((m + 1 : ℕ) : ℝ) - 1 := by
      rw [Real.log_div hm.ne' (Real.exp_pos 1).ne', Real.log_exp]
    have l3 : Real.log (Real.exp 1 / Real.sqrt 2) = Real.log (Real.exp 1 / √2) := rfl
    rw [Stirling.stirlingSeq_one] at h1
    rw [e1, l1, l2] at h1
    rw [l0] at h1
    push_cast at h1 ⊢
    nlinarith [h1]

lemma xlogx_mono : MonotoneOn (fun x : ℝ => x * Real.log x) (Set.Ici 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have h1 : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  have h2 : 0 ≤ Real.log x := Real.log_nonneg hx
  nlinarith

lemma integral_xlogx {b : ℝ} (hb : 1 ≤ b) :
    ∫ x in (1 : ℝ)..b, x * Real.log x = b ^ 2 / 2 * Real.log b - b ^ 2 / 4 + 1 / 4 := by
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) b,
      HasDerivAt (fun x : ℝ => x ^ 2 / 2 * Real.log x - x ^ 2 / 4) (x * Real.log x) x := by
    intro x hx
    have hx0 : 0 < x := by
      rw [Set.uIcc_of_le hb] at hx; linarith [hx.1]
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
      simpa using (hasDerivAt_pow 2 x).div_const 2
    have h2 := h1.mul (Real.hasDerivAt_log hx0.ne')
    have h3 : HasDerivAt (fun x : ℝ => x ^ 2 / 4) (x / 2) x := by
      have := (hasDerivAt_pow 2 x).div_const 4
      convert this using 1; simp; ring
    convert h2.sub h3 using 1
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · simp
  · exact Real.continuous_mul_log.intervalIntegrable _ _

theorem sum_nlogn_le {h : ℕ} (hh : 0 < h) :
    ∑ n ∈ range h, (n : ℝ) * Real.log n
      ≤ (h : ℝ) ^ 2 / 2 * Real.log h - (h : ℝ) ^ 2 / 4 + 1 / 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have hmono : MonotoneOn (fun x : ℝ => x * Real.log x) (Set.Icc (1 : ℝ) (1 + m)) :=
    xlogx_mono.mono (fun x hx => hx.1)
  have h1 := hmono.sum_le_integral
  have h2 := integral_xlogx (b := 1 + (m : ℝ)) (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  rw [h2] at h1
  have e : ∀ i ∈ range m, ((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ)
      = (1 + (i : ℝ)) * Real.log (1 + (i : ℝ)) := by
    intro i _; push_cast; rw [add_comm (i : ℝ) 1]
  rw [Finset.sum_congr rfl e]
  push_cast
  have e2 : (1 + (m : ℝ)) = (m : ℝ) + 1 := add_comm _ _
  rw [e2] at h1
  linarith

theorem NN_eq {h : ℕ} (hh : 0 < h) :
    ∑ a ∈ range h, ∑ b ∈ range h, elog (nodeC h a) (nodeC h b)
      = (h : ℝ) * ((h : ℝ) - 1) * Real.log h - 2 * ∑ n ∈ range h, Real.log (n.factorial) := by
  have h1 : ∀ a ∈ range h, ∑ b ∈ range h, elog (nodeC h a) (nodeC h b)
      = ((h : ℝ) - 1) * Real.log h - Real.log (a.factorial) - Real.log ((h - 1 - a).factorial) :=
    fun a ha => node_sum_eq hh a (Finset.mem_range.1 ha)
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_range_reflect (fun n => Real.log (n.factorial)) h]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem NN_ge {h : ℕ} (hh : 0 < h) :
    (3 / 2) * (h : ℝ) ^ 2 - 2 * h * Real.log h - 3 * h - 1 / 2
      ≤ ∑ a ∈ range h, ∑ b ∈ range h, elog (nodeC h a) (nodeC h b) := by
  rw [NN_eq hh]
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg (show (1 : ℝ) ≤ h by exact_mod_cast hh)
  have hS := Finset.sum_le_sum (s := range h) (fun n _ => log_factorial_le n)
  have hlog : ∑ n ∈ range h, Real.log n ≤ h * Real.log h := by
    calc ∑ n ∈ range h, Real.log n ≤ ∑ n ∈ range h, Real.log h := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · simpa using hlogh
          · exact Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast (Finset.mem_range.1 hn).le)
      _ = h * Real.log h := by simp
  have hid : ∑ n ∈ range h, (n : ℝ) = (h : ℝ) * ((h : ℝ) - 1) / 2 := by
    have := Finset.sum_range_id_mul_two h
    have h2 : ((∑ i ∈ range h, i : ℕ) : ℝ) * 2 = (h : ℝ) * ((h : ℝ) - 1) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) this
      simp only [Nat.cast_mul, Nat.cast_ofNat] at this
      rw [this, Nat.cast_sub (by omega)]; simp
    push_cast at h2
    linarith
  have hnl := sum_nlogn_le hh
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one] at hS
  nlinarith [hS, hlog, hid, hnl]

end CatalanLambda.Decay
