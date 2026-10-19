module

public import CatalanCore.Decay.Rect.NodesA

@[expose] public section

/-!
# Rectangular node sums, part 3: the cross block and the energy bounds `AX_ge`, `AY_ge` (WP-H2-core)

`Alow r m` is the explicit lower bound for the node-configuration energy
`A = ∑_{a,b} elog(τ_a, τ_b)`; it equals `r² J(m/r) - O(r log r)` with
`J(x) = 3/2 + ∫_1^{1+2x} U^τ(u) du + x² (3/2 - log 2x)`.
-/

open Finset MeasureTheory intervalIntegral
open CatalanLambda.Decay

namespace CatalanCore.Decay

lemma Utau_integrand_ii (w : ℝ) :
    IntervalIntegrable (fun t : ℝ => -Real.log ‖(w : ℂ) - (t : ℂ)‖) volume 0 1 := by
  have h : IntervalIntegrable (fun t : ℝ => Real.log (w - t)) volume (w - w) (w - (w - 1)) :=
    (intervalIntegrable_log' (a := w) (b := w - 1)).comp_sub_left w
  rw [sub_self, sub_sub_cancel] at h
  have e : (fun t : ℝ => -Real.log ‖(w : ℂ) - (t : ℂ)‖) = fun t => -Real.log (w - t) := by
    funext t; rw [norm_ofReal_sub, Real.log_abs]
  rw [e]
  exact h.neg

/-- `U^τ` is decreasing on `[1, ∞)` (real argument). -/
lemma Utau_anti : AntitoneOn (fun u : ℝ => Utau (u : ℂ)) (Set.Ici 1) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  unfold Utau
  refine intervalIntegral.integral_mono_ae_restrict (by norm_num) (Utau_integrand_ii v)
    (Utau_integrand_ii u) ?_
  have hne : ∀ᵐ t : ℝ, t ∉ ({1} : Set ℝ) := (Set.countable_singleton (1 : ℝ)).ae_notMem volume
  refine (ae_restrict_iff' measurableSet_Icc).2 ?_
  filter_upwards [hne] with t ht hmem
  have ht1 : t < 1 := lt_of_le_of_ne hmem.2 (by simpa using ht)
  show -Real.log ‖(v : ℂ) - (t : ℂ)‖ ≤ -Real.log ‖(u : ℂ) - (t : ℂ)‖
  rw [norm_ofReal_sub, norm_ofReal_sub, abs_of_pos (by linarith), abs_of_pos (by linarith)]
  have := Real.log_le_log (by linarith : 0 < u - t) (by linarith : u - t ≤ v - t)
  linarith

lemma cross_ge {r : ℕ} (hr : 0 < r) (i : ℕ) :
    (r : ℝ) * Utau (nodeC r (r + 2 * i)) - (1 + Real.log r)
      ≤ ∑ a ∈ range r, elog (nodeC r a) (nodeC r (r + 2 * i)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [Nat.mul_zero, Nat.add_zero]
    have hU : Utau (nodeC r r) = 1 := by
      have e : nodeC r r = ((1 : ℝ) : ℂ) := by unfold nodeC; rw [div_self hr'.ne']
      have := Utau_real (t := 1) zero_le_one le_rfl
      rw [e, this]; simp
    have hterm : ∀ a ∈ range r,
        elog (nodeC r a) (nodeC r r) = -Real.log ((r : ℝ) - a) + Real.log r := by
      intro a ha
      have ha' : a < r := Finset.mem_range.1 ha
      rw [elog_node hr a r (by omega)]
      have haa : (a : ℝ) < r := by exact_mod_cast ha'
      have : |(a : ℝ) - r| = (r : ℝ) - a := by
        rw [abs_sub_comm]; exact abs_of_pos (by linarith)
      rw [this]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_log_reflect]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have := log_factorial_le r
    rw [hU]; linarith
  · have hi' : (0 : ℝ) < i := by exact_mod_cast hi
    set u : ℝ := 1 + 2 / r * i with hu
    have hu1 : 1 < u := by
      have : (0 : ℝ) < 2 / r * i := mul_pos (div_pos two_pos hr') hi'
      rw [hu]; linarith
    have hnode : nodeC r (r + 2 * i) = (u : ℂ) := nodeC_X r i hr
    rw [hnode]
    set f : ℝ → ℝ := fun x => elog (x : ℂ) (u : ℂ) with hf
    have hmono : MonotoneOn f (Set.Icc 0 1) := by
      intro x hx y hy hxy
      simp only [hf, elog_real]
      have h1 : |x - u| = u - x := by rw [abs_sub_comm]; exact abs_of_pos (by linarith [hx.2])
      have h2 : |y - u| = u - y := by rw [abs_sub_comm]; exact abs_of_pos (by linarith [hy.2])
      rw [h1, h2]
      have := Real.log_le_log (by linarith [hy.2] : 0 < u - y) (by linarith : u - y ≤ u - x)
      linarith
    have key := integral_le_sum_mono hr hmono
    have hint : ∫ x in (0 : ℝ)..1, f x = Utau (u : ℂ) := by
      unfold Utau
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only [hf, elog]
      rw [norm_sub_rev]
    have hsum : ∑ j ∈ range r, f (((j + 1 : ℕ) : ℝ) / r)
        = ∑ a ∈ range r, f ((a : ℝ) / r) + f 1 - f 0 := by
      have h1 := Finset.sum_range_succ (fun a : ℕ => f ((a : ℝ) / r)) r
      have h2 := Finset.sum_range_succ' (fun a : ℕ => f ((a : ℝ) / r)) r
      have h3 : f ((r : ℝ) / r) = f 1 := by rw [div_self hr'.ne']
      have h4 : f (((0 : ℕ) : ℝ) / r) = f 0 := by simp
      rw [h3] at h1
      rw [h4] at h2
      linarith
    have hdiff : f 1 - f 0 ≤ 1 + Real.log r := by
      simp only [hf, elog_real]
      have e1 : |(1 : ℝ) - u| = u - 1 := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
      have e0 : |(0 : ℝ) - u| = u := by
        rw [zero_sub, abs_neg]; exact abs_of_pos (by linarith)
      rw [e1, e0]
      have hu1' : 0 < u - 1 := by linarith
      have h5 : -Real.log (u - 1) - -Real.log u = Real.log (u / (u - 1)) := by
        rw [Real.log_div (by linarith) hu1'.ne']; ring
      rw [h5]
      have h2r : u / (u - 1) ≤ 2 * r := by
        rw [div_le_iff₀ hu1']
        have e : 2 * (r : ℝ) * (u - 1) = 4 * i := by
          rw [hu]; field_simp; ring
        have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
        have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
        have hr2 : 2 / (r : ℝ) ≤ 2 := by rw [div_le_iff₀ hr']; linarith
        have h6 := mul_le_mul_of_nonneg_right hr2 (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
        have : u ≤ 1 + 2 * i := by rw [hu]; linarith
        linarith
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have h7 := Real.log_le_log (div_pos (by linarith) hu1') h2r
      rw [Real.log_mul (by norm_num) hr'.ne'] at h7
      linarith
    have hsumeq : ∑ a ∈ range r, elog (nodeC r a) (u : ℂ) = ∑ a ∈ range r, f ((a : ℝ) / r) := rfl
    rw [hsumeq]
    rw [hint] at key
    linarith [key, hsum, hdiff]

lemma crossY_ge {r : ℕ} (hr : 0 < r) (i : ℕ) :
    ∑ a ∈ range r, elog (nodeC r a) (nodeC r (r + 2 * i)) - Real.log ((r : ℝ) + 2 * i + 1)
      ≤ ∑ a ∈ range r, elog (nodeC r a) (nodeC r (r + 2 * i + 1)) := by
  set M : ℕ := r + 2 * i with hM
  have hterm : ∀ a ∈ range r, elog (nodeC r a) (nodeC r (M + 1)) - elog (nodeC r a) (nodeC r M)
      = Real.log ((M : ℝ) + 1 - ((a + 1 : ℕ) : ℝ)) - Real.log ((M : ℝ) + 1 - (a : ℝ)) := by
    intro a ha
    have ha' : a < r := Finset.mem_range.1 ha
    have hMa : a < M := by omega
    have haM : (a : ℝ) < M := by exact_mod_cast hMa
    rw [elog_node hr a (M + 1) (by omega), elog_node hr a M (by omega)]
    have e1 : |(a : ℝ) - ((M + 1 : ℕ) : ℝ)| = (M : ℝ) + 1 - a := by
      rw [abs_sub_comm]; push_cast; exact abs_of_pos (by linarith)
    have e2 : |(a : ℝ) - (M : ℝ)| = (M : ℝ) - a := by
      rw [abs_sub_comm]; exact abs_of_pos (by linarith)
    rw [e1, e2]
    have e3 : (M : ℝ) + 1 - ((a + 1 : ℕ) : ℝ) = (M : ℝ) - a := by push_cast; ring
    rw [e3]; ring
  have hsum : ∑ a ∈ range r, (elog (nodeC r a) (nodeC r (M + 1)) - elog (nodeC r a) (nodeC r M))
      = Real.log ((M : ℝ) + 1 - (r : ℝ)) - Real.log ((M : ℝ) + 1) := by
    rw [Finset.sum_congr rfl hterm]
    have := Finset.sum_range_sub (fun a : ℕ => Real.log ((M : ℝ) + 1 - (a : ℝ))) r
    simp only [Nat.cast_zero, sub_zero] at this
    exact this
  have hpos : 0 ≤ Real.log ((r : ℝ) + 2 * i + 1 - r) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith)
  have hMc : (M : ℝ) + 1 = r + 2 * i + 1 := by rw [hM]; push_cast; ring
  rw [Finset.sum_sub_distrib, hMc] at hsum
  linarith

/-- Cross block against `U^τ`. -/
theorem cross_sum_ge {r : ℕ} (m : ℕ) (hr : 0 < r) :
    (r : ℝ) * ((r : ℝ) / 2 * ∫ u in (1 : ℝ)..1 + 2 / r * m, Utau (u : ℂ)) - m * (1 + Real.log r)
      ≤ ∑ a ∈ range r, ∑ j ∈ range m, elog (nodeC r a) (nodeC r (r + 2 * j)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Finset.sum_comm]
  have h1 : ∀ j ∈ range m, (r : ℝ) * Utau (nodeC r (r + 2 * j)) - (1 + Real.log r)
      ≤ ∑ a ∈ range r, elog (nodeC r a) (nodeC r (r + 2 * j)) := fun j _ => cross_ge hr j
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h2
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  have hU : (1 / (2 / (r : ℝ))) * ∫ x in (1 : ℝ)..1 + (2 / (r : ℝ)) * m, Utau (x : ℂ)
      ≤ ∑ j ∈ range m, Utau (nodeC r (r + 2 * j)) := by
    have := integral_le_sum_anti (f := fun u : ℝ => Utau (u : ℂ)) (a := 1) (step := 2 / (r : ℝ))
      (by positivity) m Utau_anti
    refine this.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [nodeC_X r j hr]
  have hone : 1 / (2 / (r : ℝ)) = (r : ℝ) / 2 := one_div_div _ _
  rw [hone] at hU
  have h3 := mul_le_mul_of_nonneg_left hU hr'.le
  linarith

/-- The lower bound for the energy of the node configuration (`J(m/r) r²` up to `O(r log r)`). -/
noncomputable def Alow (r m : ℕ) : ℝ :=
  ((3 / 2) * (r : ℝ) ^ 2 - 2 * r * Real.log r - 3 * r - 1 / 2)
  + ((3 / 2) * (m : ℝ) ^ 2 - 2 * m * Real.log m - 3 * m - 1 / 2
      - m * (m - 1) * Real.log (2 * m / r))
  + 2 * ((r : ℝ) * ((r : ℝ) / 2 * ∫ u in (1 : ℝ)..1 + 2 / r * m, Utau (u : ℂ))
      - m * (1 + Real.log r))

theorem AX_ge {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    Alow r m ≤ ∑ a ∈ range (r + m), ∑ b ∈ range (r + m),
      elog (nodeC r (xnode r a)) (nodeC r (xnode r b)) := by
  refine le_of_le_of_eq ?_
    (sum_range_xnode2 r m (fun p q => elog (nodeC r p) (nodeC r q))).symm
  beta_reduce
  have hCC := NN_ge hr
  have hXX := XX_ge hr hm
  have hCX := cross_sum_ge m hr
  have hXC : ∑ i ∈ range m, ∑ b ∈ range r, elog (nodeC r (r + 2 * i)) (nodeC r b)
      = ∑ a ∈ range r, ∑ j ∈ range m, elog (nodeC r a) (nodeC r (r + 2 * j)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun j _ => elog_comm _ _))
  rw [hXC]
  unfold Alow
  linarith

theorem AY_ge {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    Alow r m - 2 * m * Real.log (r + 2 * m) ≤ ∑ a ∈ range (r + m), ∑ b ∈ range (r + m),
      elog (nodeC r (ynode r a)) (nodeC r (ynode r b)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  refine le_of_le_of_eq ?_
    (sum_range_ynode2 r m (fun p q => elog (nodeC r p) (nodeC r q))).symm
  beta_reduce
  have hCC := NN_ge hr
  have hXX := XX_ge hr hm
  have hCX := cross_sum_ge m hr
  have hYY : ∑ i ∈ range m, ∑ j ∈ range m,
        elog (nodeC r (r + 2 * i + 1)) (nodeC r (r + 2 * j + 1))
      = ∑ i ∈ range m, ∑ j ∈ range m, elog (nodeC r (r + 2 * i)) (nodeC r (r + 2 * j)) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => elog_YY r i j hr))
  have hCY : ∑ a ∈ range r, ∑ j ∈ range m, elog (nodeC r a) (nodeC r (r + 2 * j))
        - m * Real.log (r + 2 * m)
      ≤ ∑ a ∈ range r, ∑ j ∈ range m, elog (nodeC r a) (nodeC r (r + 2 * j + 1)) := by
    rw [Finset.sum_comm, Finset.sum_comm (s := range r) (t := range m)
      (f := fun a j => elog (nodeC r a) (nodeC r (r + 2 * j + 1)))]
    have h1 : ∀ j ∈ range m, ∑ a ∈ range r, elog (nodeC r a) (nodeC r (r + 2 * j))
          - Real.log (r + 2 * m)
        ≤ ∑ a ∈ range r, elog (nodeC r a) (nodeC r (r + 2 * j + 1)) := by
      intro j hj
      have hj' : j < m := Finset.mem_range.1 hj
      have hl : Real.log ((r : ℝ) + 2 * j + 1) ≤ Real.log (r + 2 * m) := by
        apply Real.log_le_log (by positivity)
        have : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj'
        linarith
      have := crossY_ge hr j
      linarith
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_sub_distrib] at h2
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    exact h2
  have hYC : ∑ i ∈ range m, ∑ b ∈ range r, elog (nodeC r (r + 2 * i + 1)) (nodeC r b)
      = ∑ a ∈ range r, ∑ j ∈ range m, elog (nodeC r a) (nodeC r (r + 2 * j + 1)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun j _ => elog_comm _ _))
  rw [hYC, hYY]
  unfold Alow
  have hXC : ∑ i ∈ range m, ∑ b ∈ range r, elog (nodeC r (r + 2 * i)) (nodeC r b)
      = ∑ a ∈ range r, ∑ j ∈ range m, elog (nodeC r a) (nodeC r (r + 2 * j)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun j _ => elog_comm _ _))
  linarith

end CatalanCore.Decay
