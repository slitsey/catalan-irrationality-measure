module

public import CatalanLambda.Decay.ThmNRiemann
public import CatalanLambda.Decay.ThmNLogFact
public import Mathlib.Analysis.SumIntegralComparisons

@[expose] public section

/-!
# Rectangular node sums, part 1: Riemann tools and the sums over the `X'` nodes (WP-H2-core)

Nodes (scaled by `r`): the common block `C = {b/r : b < r}` and the extra block
`X' = {1 + 2i/r : i < m}` (`Y'` is `X'` shifted by `1/r`).  Write `elog σ u = -log ‖σ - u‖`.

* `sumX_le` : `∑_{i<m} f(1 + 2i/r) ≤ (r/2) ∫_1^{1+2m/r} f + (f(1) - f(1+2m/r))` for `f` antitone on `[1,∞)`.
* `sumX_free_le` : [R1] for a free point `σ` (`Re σ < 0`): the `X'` nodes cost at most
  `r · Uex L σ + log(1 + 2m/r)` for every `0 ≤ L ≤ 2m/r` (**no error from the extra nodes**).
* `sumX_node_le` : [R3] for a common node, with an `O(log r)` error.
-/

open Finset MeasureTheory intervalIntegral
open CatalanLambda.Decay

namespace CatalanCore.Decay

/-! ### Riemann tools -/

lemma sum_succ_le_integral_anti {f : ℝ → ℝ} {a step : ℝ} (hs : 0 < step) (n : ℕ)
    (hf : AntitoneOn f (Set.Ici a)) :
    ∑ i ∈ range n, f (a + step * ((i + 1 : ℕ) : ℝ)) ≤ (1 / step) * ∫ x in a..a + step * n, f x := by
  have hg : AntitoneOn (fun x : ℝ => f (a + step * x)) (Set.Icc 0 (0 + (n : ℝ))) := by
    intro x hx y hy hxy
    apply hf
    · simp only [Set.mem_Ici]; have := hx.1; nlinarith
    · simp only [Set.mem_Ici]; have := hy.1; nlinarith
    · nlinarith
  have h1 := hg.sum_le_integral
  have h2 := integral_comp_add_mul (a := (0 : ℝ)) (b := 0 + (n : ℝ)) f hs.ne' a
  simp only [smul_eq_mul, mul_zero, add_zero, zero_add] at h2 h1
  rw [h2] at h1
  rw [one_div]
  exact h1

lemma integral_le_sum_anti {f : ℝ → ℝ} {a step : ℝ} (hs : 0 < step) (n : ℕ)
    (hf : AntitoneOn f (Set.Ici a)) :
    (1 / step) * ∫ x in a..a + step * n, f x ≤ ∑ i ∈ range n, f (a + step * (i : ℝ)) := by
  have hg : AntitoneOn (fun x : ℝ => f (a + step * x)) (Set.Icc 0 (0 + (n : ℝ))) := by
    intro x hx y hy hxy
    apply hf
    · simp only [Set.mem_Ici]; have := hx.1; nlinarith
    · simp only [Set.mem_Ici]; have := hy.1; nlinarith
    · nlinarith
  have h1 := hg.integral_le_sum
  have h2 := integral_comp_add_mul (a := (0 : ℝ)) (b := 0 + (n : ℝ)) f hs.ne' a
  simp only [smul_eq_mul, mul_zero, add_zero, zero_add] at h2 h1
  rw [h2] at h1
  rw [one_div]
  exact h1

lemma integral_le_sum_mono {f : ℝ → ℝ} {r : ℕ} (hr : 0 < r) (hf : MonotoneOn f (Set.Icc 0 1)) :
    (r : ℝ) * ∫ x in (0 : ℝ)..1, f x ≤ ∑ j ∈ range r, f (((j + 1 : ℕ) : ℝ) / r) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hg : MonotoneOn (fun x : ℝ => f (x / r)) (Set.Icc 0 (0 + (r : ℝ))) := by
    intro x hx y hy hxy
    apply hf
    · constructor
      · exact div_nonneg hx.1 hr'.le
      · have := hx.2; rw [zero_add] at this; rw [div_le_one hr']; exact this
    · constructor
      · exact div_nonneg hy.1 hr'.le
      · have := hy.2; rw [zero_add] at this; rw [div_le_one hr']; exact this
    · exact div_le_div_of_nonneg_right hxy hr'.le
  have h1 := hg.integral_le_sum
  have h2 := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := 0 + (r : ℝ)) f hr'.ne'
  simp only [smul_eq_mul, zero_div, zero_add, div_self hr'.ne'] at h2 h1
  rw [h2] at h1
  exact h1

lemma norm_sub_real_pos' {σ : ℂ} {u : ℝ} (h : σ.re < u) : 0 < ‖σ - (u : ℂ)‖ := by
  apply norm_pos_iff.2
  intro e
  have := congrArg Complex.re e
  simp at this
  linarith

lemma elog_real_anti {σ : ℂ} {u u' : ℝ} (h : σ.re < u) (huu : u ≤ u') :
    elog σ (u' : ℂ) ≤ elog σ (u : ℂ) := by
  unfold elog
  have h1 : 0 < ‖σ - (u : ℂ)‖ := norm_sub_real_pos' h
  have h2 : ‖σ - (u : ℂ)‖ ≤ ‖σ - (u' : ℂ)‖ := by
    have hsq : ‖σ - (u : ℂ)‖ ^ 2 ≤ ‖σ - (u' : ℂ)‖ ^ 2 := by
      rw [norm_sub_real_sq, norm_sub_real_sq]
      nlinarith [sq_nonneg σ.im, mul_nonneg (sub_nonneg.2 huu) (by linarith : (0 : ℝ) ≤ u' + u - 2 * σ.re)]
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg (σ - (u' : ℂ))]
  have := Real.log_le_log h1 h2
  linarith

lemma elog_real_nonpos {σ : ℂ} (hσ : σ.re ≤ 0) {u : ℝ} (hu : 1 ≤ u) : elog σ (u : ℂ) ≤ 0 := by
  unfold elog
  have h1 : 1 ≤ ‖σ - (u : ℂ)‖ := by
    have : |(σ - (u : ℂ)).re| ≤ ‖σ - (u : ℂ)‖ := Complex.abs_re_le_norm _
    simp at this
    rw [abs_of_neg (by linarith)] at this
    linarith
  have := Real.log_nonneg h1
  linarith

lemma one_le_norm_sub_real {σ : ℂ} (hσ : σ.re ≤ 0) {u : ℝ} (hu : 1 ≤ u) : 1 ≤ ‖σ - (u : ℂ)‖ := by
  have : |(σ - (u : ℂ)).re| ≤ ‖σ - (u : ℂ)‖ := Complex.abs_re_le_norm _
  simp at this
  rw [abs_of_neg (by linarith)] at this
  linarith

lemma integrable_elog {σ : ℂ} (hσ : σ.re < 1) {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable (fun u : ℝ => elog σ (u : ℂ)) volume a b := by
  have hanti : AntitoneOn (fun u : ℝ => elog σ (u : ℂ)) (Set.Ici 1) :=
    fun u hu v hv huv => elog_real_anti (lt_of_lt_of_le hσ hu) huv
  refine (hanti.mono ?_).intervalIntegrable
  intro x hx
  rw [Set.mem_uIcc] at hx
  simp only [Set.mem_Ici]
  rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith

/-- The extra-node potential `U^ex_L(σ) = ½ ∫_1^{1+L} -log‖σ-u‖ du` (mass `L/2`). -/
noncomputable def Uex (L : ℝ) (σ : ℂ) : ℝ := (1 / 2) * ∫ u in (1 : ℝ)..1 + L, elog σ (u : ℂ)

lemma nodeC_X (r i : ℕ) (hr : 0 < r) :
    nodeC r (r + 2 * i) = (((1 : ℝ) + 2 / r * i : ℝ) : ℂ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  unfold nodeC
  congr 1
  push_cast
  field_simp

lemma nodeC_Y (r i : ℕ) (hr : 0 < r) :
    nodeC r (r + 2 * i + 1) = (((1 : ℝ) + 2 / r * i + 1 / r : ℝ) : ℂ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  unfold nodeC
  congr 1
  push_cast
  field_simp

/-- **Core Riemann comparison** for the `X'` nodes. -/
theorem sumX_le {σ : ℂ} (hσ : σ.re < 1) {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    ∑ i ∈ range m, elog σ (nodeC r (r + 2 * i))
      ≤ ((r : ℝ) / 2) * (∫ u in (1 : ℝ)..1 + 2 * m / r, elog σ (u : ℂ))
        + (elog σ ((1 : ℝ) : ℂ) - elog σ (((1 + 2 * m / r : ℝ)) : ℂ)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set step : ℝ := 2 / r with hstep
  have hs : 0 < step := by positivity
  set f : ℝ → ℝ := fun u => elog σ (u : ℂ) with hf
  have hanti : AntitoneOn f (Set.Ici 1) :=
    fun u hu v hv huv => elog_real_anti (lt_of_lt_of_le hσ hu) huv
  have hS : ∑ i ∈ range m, elog σ (nodeC r (r + 2 * i)) = ∑ i ∈ range m, f (1 + step * i) :=
    Finset.sum_congr rfl (fun i _ => by rw [nodeC_X r i hr])
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hE : (1 : ℝ) + 2 * ((n + 1 : ℕ) : ℝ) / r = 1 + step * ((n : ℝ) + 1) := by
    rw [hstep]; push_cast; ring
  have hone : 1 / step = (r : ℝ) / 2 := by rw [hstep, one_div_div]
  rw [hS, Finset.sum_range_succ']
  have core := sum_succ_le_integral_anti hs n hanti
  have hii : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → IntervalIntegrable f volume a b :=
    fun a b ha hb => integrable_elog hσ ha hb
  have hsplit : ∫ x in (1 : ℝ)..1 + step * ((n : ℝ) + 1), f x
      = (∫ x in (1 : ℝ)..1 + step * n, f x)
        + ∫ x in (1 + step * n)..1 + step * ((n : ℝ) + 1), f x := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hii _ _ le_rfl (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    · exact hii _ _ (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hlast : step * f (1 + step * ((n : ℝ) + 1))
      ≤ ∫ x in (1 + step * n)..1 + step * ((n : ℝ) + 1), f x := by
    have hab : (1 + step * (n : ℝ)) ≤ 1 + step * ((n : ℝ) + 1) := by nlinarith
    have := intervalIntegral.integral_mono_on hab (f := fun _ => f (1 + step * ((n : ℝ) + 1)))
      (g := f) (by simp) (hii _ _ (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
        (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
      (fun x hx => hanti (by simp only [Set.mem_Ici]; nlinarith [Nat.cast_nonneg (α := ℝ) n, hx.1])
        (by simp only [Set.mem_Ici]; nlinarith [Nat.cast_nonneg (α := ℝ) n]) hx.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have e : 1 + step * ((n : ℝ) + 1) - (1 + step * n) = step := by ring
    rw [e] at this
    exact this
  have key : (1 / step) * ∫ x in (1 : ℝ)..1 + step * n, f x
      ≤ (1 / step) * (∫ x in (1 : ℝ)..1 + step * ((n : ℝ) + 1), f x) - f (1 + step * ((n : ℝ) + 1)) := by
    have h1 : ∫ x in (1 : ℝ)..1 + step * n, f x
        ≤ (∫ x in (1 : ℝ)..1 + step * ((n : ℝ) + 1), f x) - step * f (1 + step * ((n : ℝ) + 1)) := by
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 1 / step)
    have e : 1 / step * (step * f (1 + step * ((n : ℝ) + 1))) = f (1 + step * ((n : ℝ) + 1)) := by
      field_simp
    rw [mul_sub, e] at h2
    exact h2
  rw [hone] at core key
  rw [hE]
  have e0 : elog σ (((1 + step * ((0 : ℕ) : ℝ) : ℝ)) : ℂ) = elog σ ((1 : ℝ) : ℂ) := by simp
  simp only [hf]
  rw [e0]
  linarith

theorem sumY_le_sumX {σ : ℂ} (hσ : σ.re < 1) {r : ℕ} (hr : 0 < r) (m : ℕ) :
    ∑ i ∈ range m, elog σ (nodeC r (r + 2 * i + 1)) ≤ ∑ i ∈ range m, elog σ (nodeC r (r + 2 * i)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [nodeC_X r i hr, nodeC_Y r i hr]
  apply elog_real_anti
  · have : (0 : ℝ) ≤ 2 / r * i := by positivity
    linarith
  · have : (0 : ℝ) < 1 / r := by positivity
    linarith

/-- [R1] for free points. -/
theorem sumX_free_le {σ : ℂ} (hσ : σ.re < 0) {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ 2 * m / r) :
    ∑ i ∈ range m, elog σ (nodeC r (r + 2 * i))
      ≤ (r : ℝ) * Uex L σ + Real.log (1 + 2 * m / r) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hσ1 : σ.re < 1 := by linarith
  have h0 := sumX_le hσ1 hr hm
  have hL' : (0 : ℝ) ≤ 2 * m / r := by positivity
  have hsplit : ∫ u in (1 : ℝ)..1 + 2 * m / r, elog σ (u : ℂ)
      = (∫ u in (1 : ℝ)..1 + L, elog σ (u : ℂ)) + ∫ u in (1 + L)..1 + 2 * m / r, elog σ (u : ℂ) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact integrable_elog hσ1 le_rfl (by linarith)
    · exact integrable_elog hσ1 (by linarith) (by linarith)
  have hneg : ∫ u in (1 + L)..1 + 2 * m / r, elog σ (u : ℂ) ≤ 0 := by
    have := intervalIntegral.integral_mono_on (by linarith : 1 + L ≤ 1 + 2 * (m : ℝ) / r)
      (f := fun u : ℝ => elog σ (u : ℂ)) (g := fun _ => (0 : ℝ))
      (integrable_elog hσ1 (by linarith) (by linarith)) (by simp)
      (fun x hx => elog_real_nonpos hσ.le (by linarith [hx.1]))
    simpa using this
  have hbound : elog σ ((1 : ℝ) : ℂ) - elog σ (((1 + 2 * m / r : ℝ)) : ℂ) ≤ Real.log (1 + 2 * m / r) := by
    unfold elog
    have h1 : 1 ≤ ‖σ - ((1 : ℝ) : ℂ)‖ := one_le_norm_sub_real hσ.le le_rfl
    have h2 : ‖σ - (((1 + 2 * m / r : ℝ)) : ℂ)‖ ≤ ‖σ - ((1 : ℝ) : ℂ)‖ + 2 * m / r := by
      have : σ - (((1 + 2 * m / r : ℝ)) : ℂ) = (σ - ((1 : ℝ) : ℂ)) - ((2 * m / r : ℝ) : ℂ) := by
        push_cast; ring
      rw [this]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hL']
    have h3 : 0 < ‖σ - (((1 + 2 * m / r : ℝ)) : ℂ)‖ := by
      have : σ.re < ((1 + 2 * m / r : ℝ)) := by linarith
      exact norm_sub_real_pos' this
    have h4 : -Real.log ‖σ - ((1 : ℝ) : ℂ)‖ - -Real.log ‖σ - (((1 + 2 * m / r : ℝ)) : ℂ)‖
        = Real.log (‖σ - (((1 + 2 * m / r : ℝ)) : ℂ)‖ / ‖σ - ((1 : ℝ) : ℂ)‖) := by
      rw [Real.log_div h3.ne' (by linarith)]; ring
    rw [h4]
    apply Real.log_le_log (div_pos h3 (by linarith))
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hUex : (r : ℝ) / 2 * (∫ u in (1 : ℝ)..1 + L, elog σ (u : ℂ)) = r * Uex L σ := by
    unfold Uex; ring
  rw [hsplit, mul_add] at h0
  have hB' : (r : ℝ) / 2 * (∫ u in (1 + L)..1 + 2 * m / r, elog σ (u : ℂ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
  linarith

/-- [R3] for a common node `b/r`, `b < r`: `O(log r)` error. -/
theorem sumX_node_le {r m b : ℕ} (hr : 0 < r) (hm : 0 < m) (hb : b < r)
    {L : ℝ} (hL0 : 0 < L) (hL : L ≤ 2 * m / r) (hL2 : 2 * (m : ℝ) / r ≤ L + 2 / r) :
    ∑ i ∈ range m, elog (nodeC r b) (nodeC r (r + 2 * i))
      ≤ (r : ℝ) * Uex L (nodeC r b) + Real.log (1 + 2 * m) + |Real.log L| := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hbr : (b : ℝ) + 1 ≤ r := by exact_mod_cast hb
  set σ : ℂ := nodeC r b with hσdef
  have hσre : σ.re = (b : ℝ) / r := by simp [hσdef, nodeC]
  have hσ1 : σ.re < 1 := by
    rw [hσre, div_lt_one hr']; exact_mod_cast hb
  have hσ0 : 0 ≤ σ.re := by rw [hσre]; positivity
  have hσim : σ.im = 0 := by simp [hσdef, nodeC]
  have h0 := sumX_le hσ1 hr hm
  set L' : ℝ := 2 * m / r with hL'def
  have hL'0 : 0 ≤ L' := by positivity
  have hsplit : ∫ u in (1 : ℝ)..1 + L', elog σ (u : ℂ)
      = (∫ u in (1 : ℝ)..1 + L, elog σ (u : ℂ)) + ∫ u in (1 + L)..1 + L', elog σ (u : ℂ) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact integrable_elog hσ1 le_rfl (by linarith)
    · exact integrable_elog hσ1 (by linarith) (by linarith)
  have hpt : ∀ u : ℝ, 1 + L ≤ u → elog σ (u : ℂ) ≤ |Real.log L| := by
    intro u hu
    unfold elog
    have hn : ‖σ - (u : ℂ)‖ = u - σ.re := by
      have : σ - (u : ℂ) = ((σ.re - u : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hσim]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; ring
    rw [hn]
    have hL1 : L ≤ u - σ.re := by linarith
    have := Real.log_le_log hL0 hL1
    have h2 := neg_abs_le (Real.log L)
    linarith
  have hpos : ∫ u in (1 + L)..1 + L', elog σ (u : ℂ) ≤ (L' - L) * |Real.log L| := by
    have := intervalIntegral.integral_mono_on (by linarith : 1 + L ≤ 1 + L')
      (f := fun u : ℝ => elog σ (u : ℂ)) (g := fun _ => |Real.log L|)
      (integrable_elog hσ1 (by linarith) (by linarith)) (by simp)
      (fun x hx => hpt x hx.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have e : 1 + L' - (1 + L) = L' - L := by ring
    rw [e] at this
    exact this
  have hbound : elog σ ((1 : ℝ) : ℂ) - elog σ (((1 + L' : ℝ)) : ℂ) ≤ Real.log (1 + 2 * m) := by
    unfold elog
    have hn1 : ‖σ - ((1 : ℝ) : ℂ)‖ = 1 - σ.re := by
      have : σ - ((1 : ℝ) : ℂ) = ((σ.re - 1 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hσim]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; ring
    have h1r : 1 / (r : ℝ) ≤ 1 - σ.re := by
      rw [hσre]
      have : (b : ℝ) / r ≤ 1 - 1 / r := by
        rw [div_le_iff₀ hr']
        have : (1 - 1 / (r : ℝ)) * r = r - 1 := by field_simp
        rw [this]; linarith
      linarith
    have h2 : ‖σ - (((1 + L' : ℝ)) : ℂ)‖ ≤ ‖σ - ((1 : ℝ) : ℂ)‖ + L' := by
      have : σ - (((1 + L' : ℝ)) : ℂ) = (σ - ((1 : ℝ) : ℂ)) - ((L' : ℝ) : ℂ) := by
        push_cast; ring
      rw [this]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hL'0]
    have h3 : 0 < ‖σ - (((1 + L' : ℝ)) : ℂ)‖ := by
      have : σ.re < ((1 + L' : ℝ)) := by linarith
      exact norm_sub_real_pos' this
    have hpos1 : 0 < ‖σ - ((1 : ℝ) : ℂ)‖ := by rw [hn1]; linarith
    have h4 : -Real.log ‖σ - ((1 : ℝ) : ℂ)‖ - -Real.log ‖σ - (((1 + L' : ℝ)) : ℂ)‖
        = Real.log (‖σ - (((1 + L' : ℝ)) : ℂ)‖ / ‖σ - ((1 : ℝ) : ℂ)‖) := by
      rw [Real.log_div h3.ne' hpos1.ne']; ring
    rw [h4]
    apply Real.log_le_log (div_pos h3 hpos1)
    rw [div_le_iff₀ hpos1]
    -- ‖σ-1‖ ≥ 1/r  ⇒  L' ≤ 2m ‖σ-1‖
    have hLm : L' ≤ 2 * m * ‖σ - ((1 : ℝ) : ℂ)‖ := by
      rw [hn1]
      have : L' = 2 * m * (1 / r) := by rw [hL'def]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left h1r (by positivity)
    nlinarith
  rw [hsplit, mul_add] at h0
  have hfac : (r : ℝ) / 2 * ((L' - L) * |Real.log L|) ≤ |Real.log L| := by
    have h1 : (L' - L) ≤ 2 / r := by linarith
    have h2 : (r : ℝ) / 2 * (L' - L) ≤ 1 := by
      calc (r : ℝ) / 2 * (L' - L) ≤ (r : ℝ) / 2 * (2 / r) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 1 := by field_simp
    nlinarith [abs_nonneg (Real.log L)]
  have hUex : (r : ℝ) / 2 * (∫ u in (1 : ℝ)..1 + L, elog σ (u : ℂ)) = r * Uex L σ := by
    unfold Uex; ring
  have hmul := mul_le_mul_of_nonneg_left hpos (by positivity : (0 : ℝ) ≤ (r : ℝ) / 2)
  linarith

end CatalanCore.Decay
