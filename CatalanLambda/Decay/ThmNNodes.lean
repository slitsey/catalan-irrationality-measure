import CatalanLambda.Decay.ThmNLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Theorem N_ρ, stage 3a: the potential `U^τ` of Lebesgue measure on `[0,1]` and the node sums [R3]
-/

open Finset MeasureTheory intervalIntegral

namespace CatalanLambda.Decay

/-- `U^τ(z) = ∫_0^1 -log |z - t| dt`. -/
noncomputable def Utau (z : ℂ) : ℝ := ∫ t in (0 : ℝ)..1, -Real.log ‖z - (t : ℂ)‖

/-- Closed form of `U^τ` on `[0,1]`. -/
theorem Utau_real {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Utau (t : ℂ) = 1 - t * Real.log t - (1 - t) * Real.log (1 - t) := by
  unfold Utau
  have h1 : ∀ u : ℝ, -Real.log ‖(t : ℂ) - (u : ℂ)‖ = (fun v : ℝ => -Real.log v) (t - u) := by
    intro u
    simp only
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
  simp_rw [h1]
  rw [intervalIntegral.integral_comp_sub_left (fun v : ℝ => -Real.log v) t]
  rw [intervalIntegral.integral_neg, integral_log]
  have : Real.log (t - 1) = Real.log (1 - t) := by
    rw [← Real.log_neg_eq_log]; ring_nf
  simp only [sub_zero]
  rw [this]
  ring_nf

/-- `n! ≥ (n/e)^n` in logarithmic form. -/
lemma log_factorial_ge (n : ℕ) : (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := Real.pow_div_factorial_le_exp (n : ℝ) hn'.le n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have h2 : (n : ℝ) ^ n / n.factorial ≤ Real.exp n := h
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_div (by positivity) hf.ne', Real.log_pow, Real.log_exp] at h3
    linarith

/-- The scaled node `b / h` as a complex number. -/
noncomputable def nodeC (h b : ℕ) : ℂ := (((b : ℝ) / h : ℝ) : ℂ)

lemma sum_log_succ (n : ℕ) : ∑ j ∈ range n, Real.log ((j : ℝ) + 1) = Real.log (n.factorial) := by
  have : ∏ j ∈ range n, ((j : ℝ) + 1) = (n.factorial : ℝ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl
  rw [← this, Real.log_prod]
  intro j _; positivity

lemma sum_log_reflect (a : ℕ) : ∑ b ∈ range a, Real.log ((a : ℝ) - b) = Real.log (a.factorial) := by
  rw [← sum_log_succ, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j < a := Finset.mem_range.1 hj
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

lemma elog_node {h : ℕ} (hh : 0 < h) (a b : ℕ) (hab : a ≠ b) :
    elog (nodeC h a) (nodeC h b) = -Real.log |(a : ℝ) - b| + Real.log h := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  unfold elog nodeC
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hne : (a : ℝ) - b ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hab)
  have : (a : ℝ) / h - b / h = ((a : ℝ) - b) / h := by ring
  rw [this, abs_div, abs_of_pos hh', Real.log_div (abs_ne_zero.2 hne) hh'.ne']
  ring

lemma elog_node_self (h a : ℕ) : elog (nodeC h a) (nodeC h a) = 0 := elog_self _

/-- **[R3]** `∑_b e(t_a, t_b) ≤ h U^τ(t_a)`: error-free removed-node bound. -/
theorem node_sum_le {h : ℕ} (hh : 0 < h) (a : ℕ) (ha : a < h) :
    ∑ b ∈ range h, elog (nodeC h a) (nodeC h b) ≤ h * Utau (nodeC h a) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hlogh := Real.log_nonneg (show (1 : ℝ) ≤ h by exact_mod_cast hh)
  -- evaluate the sum
  have hsplit : ∑ b ∈ range h, elog (nodeC h a) (nodeC h b)
      = ∑ b ∈ range a, elog (nodeC h a) (nodeC h b) + elog (nodeC h a) (nodeC h a)
        + ∑ b ∈ Ico (a + 1) h, elog (nodeC h a) (nodeC h b) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show a + 1 ≤ h by omega), Finset.sum_range_succ]
  have p1 : ∑ b ∈ range a, elog (nodeC h a) (nodeC h b)
      = a * Real.log h - Real.log (a.factorial) := by
    rw [← sum_log_reflect]
    have : ∀ b ∈ range a, elog (nodeC h a) (nodeC h b) = -Real.log ((a : ℝ) - b) + Real.log h := by
      intro b hb
      have hb' : b < a := Finset.mem_range.1 hb
      rw [elog_node hh a b (by omega)]
      rw [abs_of_pos (by have : (b : ℝ) < a := by exact_mod_cast hb'
                         linarith)]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    simp
    ring
  have p3 : ∑ b ∈ Ico (a + 1) h, elog (nodeC h a) (nodeC h b)
      = ((h : ℝ) - 1 - a) * Real.log h - Real.log ((h - 1 - a).factorial) := by
    rw [Finset.sum_Ico_eq_sum_range, ← sum_log_succ]
    have : ∀ j ∈ range (h - (a + 1)), elog (nodeC h a) (nodeC h (a + 1 + j))
        = -Real.log ((j : ℝ) + 1) + Real.log h := by
      intro j hj
      rw [elog_node hh a (a + 1 + j) (by omega)]
      push_cast
      have : |(a : ℝ) - (a + 1 + j)| = (j : ℝ) + 1 := by
        rw [abs_of_neg (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)]; ring
      rw [this]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e : h - (a + 1) = h - 1 - a := by omega
    rw [e]
    have e2 : ((h - 1 - a : ℕ) : ℝ) = (h : ℝ) - 1 - a := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [e2]; ring
  rw [hsplit, p1, p3, elog_node_self, add_zero]
  -- closed form of U^tau
  have ht0 : (0 : ℝ) ≤ (a : ℝ) / h := by positivity
  have ht1 : (a : ℝ) / h ≤ 1 := by
    rw [div_le_one hh']; exact_mod_cast ha.le
  have hU := Utau_real ht0 ht1
  have hnode : nodeC h a = (((a : ℝ) / h : ℝ) : ℂ) := rfl
  rw [hnode, hU]
  have hha : (0 : ℝ) < (h : ℝ) - a := by
    have : (a : ℝ) < h := by exact_mod_cast ha
    linarith
  have e1 : (h : ℝ) * (((a : ℝ) / h) * Real.log ((a : ℝ) / h))
      = a * (Real.log a - Real.log h) := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0; simp
    · have : (0 : ℝ) < a := by exact_mod_cast h0
      rw [Real.log_div this.ne' hh'.ne']; field_simp
  have e2 : (h : ℝ) * ((1 - (a : ℝ) / h) * Real.log (1 - (a : ℝ) / h))
      = ((h : ℝ) - a) * (Real.log ((h : ℝ) - a) - Real.log h) := by
    have : 1 - (a : ℝ) / h = ((h : ℝ) - a) / h := by field_simp
    rw [this, Real.log_div hha.ne' hh'.ne']; field_simp
  have e3 : (h : ℝ) * (1 - (a : ℝ) / h * Real.log ((a : ℝ) / h)
      - (1 - (a : ℝ) / h) * Real.log (1 - (a : ℝ) / h))
      = h - a * (Real.log a - Real.log h) - ((h : ℝ) - a) * (Real.log ((h : ℝ) - a) - Real.log h) := by
    rw [mul_sub, mul_sub, mul_one, ← e1, ← e2]
  rw [e3]
  -- factorial bounds
  have f1 := log_factorial_ge a
  have f2 := log_factorial_ge (h - a)
  have hfac : (h - a).factorial = (h - a) * (h - 1 - a).factorial := by
    have : h - a = (h - 1 - a) + 1 := by omega
    conv_lhs => rw [this, Nat.factorial_succ]
    rw [← this]
  have hf2 : Real.log ((h - a).factorial) = Real.log ((h : ℝ) - a) + Real.log ((h - 1 - a).factorial) := by
    rw [hfac]; push_cast
    rw [Nat.cast_sub ha.le, Real.log_mul hha.ne' (by positivity)]
  rw [Nat.cast_sub ha.le] at f2
  have hlog : Real.log ((h : ℝ) - a) ≤ Real.log h := by
    apply Real.log_le_log hha
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  nlinarith [f1, f2, hf2, hlog]

end CatalanLambda.Decay
