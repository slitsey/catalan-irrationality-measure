module

public import CatalanCore.Decay.Rect.NodesB
public import CatalanCore.Decay.Rect.Energy2
public import CatalanCore.Decay.Window

@[expose] public section

/-!
# Asymptotics of the rectangular decay exponent (WP-H2-core)

* `Jfun x = 3/2 + (3/2)x² - x² log 2x + ∫_1^{1+2x} U^τ`, the energy of the node measure
  `Leb[0,1] + ½ Leb[1,1+2x]`  (`I(ν_x)`).
* `Alow_ge` : `Alow r m ≥ r² (Jfun α - δ) - (C₃ r + C₄ r log r)` for `α r ≤ m ≤ α r + 1`.
* `RerrR_le` : `RerrR ≤ C₁ r + C₂ r log r`.
* `asymp_main` : the exponent bookkeeping: for every `δ > 0` and large `r`
  `r log 2 + N L₀ + RerrR - (2rNm' + 2r²dS - N²I + Alow) ≤ -(D - δ) r²`
  whenever `D ≤ 2((1+α)m' + dS) - (1+α)² I + Inu` and `Inu ≤ Jfun α`.
-/

open Finset Filter Topology MeasureTheory intervalIntegral
open CatalanLambda.Decay

namespace CatalanCore.Decay

noncomputable def gJ (x : ℝ) : ℝ := 3 / 2 + (3 / 2) * x ^ 2 - x ^ 2 * Real.log (2 * x)

noncomputable def Iu (x : ℝ) : ℝ := ∫ u in (1 : ℝ)..1 + 2 * x, Utau (u : ℂ)

/-- `I(ν_x)`, the energy of `Leb[0,1] + ½ Leb[1, 1+2x]`. -/
noncomputable def Jfun (x : ℝ) : ℝ := gJ x + Iu x

lemma gJ_cont {α : ℝ} (hα : 0 < α) : ContinuousAt gJ α := by
  unfold gJ
  have h2 : (2 * α) ≠ 0 := by positivity
  fun_prop (disch := positivity)

lemma Iu_ge {α x : ℝ} (hα : 0 < α) (hαx : α ≤ x) (hx : x ≤ α + 1) :
    Iu α + 2 * (x - α) * Utau (((3 + 2 * α : ℝ)) : ℂ) ≤ Iu x := by
  unfold Iu
  have hii : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b →
      IntervalIntegrable (fun u : ℝ => Utau (u : ℂ)) volume a b := by
    intro a b ha hb
    refine (Utau_anti.mono ?_).intervalIntegrable
    intro y hy
    rw [Set.mem_uIcc] at hy
    simp only [Set.mem_Ici]
    rcases hy with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hsplit : ∫ u in (1 : ℝ)..1 + 2 * x, Utau (u : ℂ)
      = (∫ u in (1 : ℝ)..1 + 2 * α, Utau (u : ℂ))
        + ∫ u in (1 + 2 * α)..1 + 2 * x, Utau (u : ℂ) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hii _ _ le_rfl (by linarith)
    · exact hii _ _ (by linarith) (by linarith)
  have hlow : (1 + 2 * x - (1 + 2 * α)) * Utau (((3 + 2 * α : ℝ)) : ℂ)
      ≤ ∫ u in (1 + 2 * α)..1 + 2 * x, Utau (u : ℂ) := by
    have := intervalIntegral.integral_mono_on (by linarith : 1 + 2 * α ≤ 1 + 2 * x)
      (f := fun _ => Utau (((3 + 2 * α : ℝ)) : ℂ)) (g := fun u : ℝ => Utau (u : ℂ))
      (by simp) (hii _ _ (by linarith) (by linarith))
      (fun u hu => Utau_anti (by simp only [Set.mem_Ici]; linarith [hu.1])
        (by simp only [Set.mem_Ici]; linarith) (by linarith [hu.2]))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this
  rw [hsplit]
  have e : 1 + 2 * x - (1 + 2 * α) = 2 * (x - α) := by ring
  rw [e] at hlow
  linarith

lemma err_small (c1 c2 δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ r : ℕ in atTop, c1 * r + c2 * r * Real.log r ≤ δ * (r : ℝ) ^ 2 := by
  have h1 : Tendsto (fun r : ℕ => c1 / (r : ℝ) + c2 * (Real.log r / r)) atTop (𝓝 0) := by
    have a : Tendsto (fun r : ℕ => c1 / (r : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using a.add (tendsto_log_div_nat.const_mul c2)
  filter_upwards [(tendsto_order.1 h1).2 δ hδ, eventually_ge_atTop 1] with r hr hr1
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr1
  have h2 : (c1 / r + c2 * (Real.log r / r)) * (r : ℝ) ^ 2 ≤ δ * (r : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hr.le (sq_nonneg _)
  have e : (c1 / r + c2 * (Real.log r / r)) * (r : ℝ) ^ 2 = c1 * r + c2 * r * Real.log r := by
    field_simp
  linarith

set_option maxHeartbeats 4000000 in
/-- Lower bound for `Alow` in terms of `Jfun α`. -/
theorem Alow_ge {α : ℝ} (hα : 0 < α) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r1 : ℕ) (C3 C4 : ℝ), ∀ r m : ℕ, r1 ≤ r → α * r ≤ m → (m : ℝ) ≤ α * r + 1 →
      (r : ℝ) ^ 2 * (Jfun α - δ) - (C3 * r + C4 * r * Real.log r) ≤ Alow r m := by
  obtain ⟨η, hη, hηg⟩ := Metric.continuousAt_iff.1 (gJ_cont hα) (δ / 2) (by positivity)
  set c0 : ℝ := Utau (((3 + 2 * α : ℝ)) : ℂ) with hc0
  set Lα1 : ℝ := Real.log (α + 1) with hLα1
  set Lx : ℝ := |Real.log (2 * α)| + Real.log (2 * α + 2) with hLx
  have hLα1nn : 0 ≤ Lα1 := Real.log_nonneg (by linarith)
  have hLxnn : 0 ≤ Lx := by
    have : 0 ≤ Real.log (2 * α + 2) := Real.log_nonneg (by linarith)
    positivity
  refine ⟨⌈1 / η⌉₊ + 1, 2 * |c0| + (4 + 2 * (α + 1) * Lα1 + 3 * (α + 1) + (α + 1) * Lx + 2 * (α + 1)),
    (2 + 2 * (α + 1) + 2 * (α + 1)), ?_⟩
  intro r m hr hαr hαr'
  have hr1 : (1 : ℝ) ≤ r := by
    have : 1 ≤ r := by omega
    exact_mod_cast this
  have hr' : (0 : ℝ) < r := by linarith
  have hrη : 1 / (r : ℝ) < η := by
    have h1 : (⌈1 / η⌉₊ : ℝ) ≤ r := by exact_mod_cast (by omega : ⌈1 / η⌉₊ ≤ r)
    have h2 : 1 / η ≤ ⌈1 / η⌉₊ := Nat.le_ceil _
    have h3 : 1 / η < r := by
      have : (⌈1 / η⌉₊ : ℝ) + 1 ≤ r := by exact_mod_cast hr
      linarith
    rw [div_lt_iff₀ hr']
    rw [div_lt_iff₀ hη] at h3
    linarith
  set x : ℝ := (m : ℝ) / r with hx
  have hxα : α ≤ x := by rw [hx, le_div_iff₀ hr']; exact hαr
  have hxα' : x ≤ α + 1 / r := by
    rw [hx, div_le_iff₀ hr']
    have : (α + 1 / (r : ℝ)) * r = α * r + 1 := by field_simp
    rw [this]; exact hαr'
  have hx1 : x ≤ α + 1 := by
    have : 1 / (r : ℝ) ≤ 1 := by rw [div_le_one hr']; exact hr1
    linarith
  have hxm : (m : ℝ) = x * r := by rw [hx]; field_simp
  -- continuity of gJ
  have hg : gJ α - δ / 2 ≤ gJ x := by
    have := hηg (x := x) (by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).1
    linarith
  -- integral
  have hI := Iu_ge hα hxα hx1
  have hIx : Iu α - 2 * (1 / r) * |c0| ≤ Iu x := by
    have h1 : 2 * (x - α) * c0 ≥ -(2 * (1 / (r : ℝ)) * |c0|) := by
      have h2 : 2 * (x - α) * |c0| ≤ 2 * (1 / (r : ℝ)) * |c0| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); linarith
      have h3 : -(2 * (x - α) * |c0|) ≤ 2 * (x - α) * c0 := by
        have := neg_abs_le c0
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (x - α)) (abs_nonneg c0)]
      linarith
    linarith
  -- the identity for Alow
  have hlog2 : Real.log (2 * m / r) = Real.log (2 * x) := by
    congr 1; rw [hx]; ring
  have hint : (1 : ℝ) + 2 / r * m = 1 + 2 * x := by rw [hx]; ring
  have hAl : Alow r m = (r : ℝ) ^ 2 * (gJ x + Iu x)
      + (-(2 * r * Real.log r) - 3 * r - 1 - 2 * m * Real.log m - 3 * m + m * Real.log (2 * x)
          - 2 * m * (1 + Real.log r)) := by
    unfold Alow gJ Iu
    rw [hlog2, hint, hxm]
    ring
  -- bounds on the error
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmMx : (m : ℝ) ≤ (α + 1) * r := by
    rw [hxm]; exact mul_le_mul_of_nonneg_right hx1 hr'.le
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hmlogm : (m : ℝ) * Real.log m ≤ (α + 1) * r * (Lα1 + Real.log r) := by
    by_cases hm : (m : ℝ) = 0
    · rw [hm, zero_mul]
      exact mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ α + 1) hr'.le) (add_nonneg hLα1nn hlogr)
    · have hmpos : 0 < (m : ℝ) := lt_of_le_of_ne hm0 (Ne.symm hm)
      have : Real.log m ≤ Lα1 + Real.log r := by
        rw [hLα1, ← Real.log_mul (by linarith) hr'.ne']
        exact Real.log_le_log hmpos hmMx
      have hlm : 0 ≤ Real.log m := Real.log_nonneg (by
        by_contra h
        push_neg at h
        have : (m : ℕ) = 0 := by
          have : (m : ℝ) < 1 := h
          have : m < 1 := by exact_mod_cast this
          omega
        simp [this] at hm)
      calc (m : ℝ) * Real.log m ≤ ((α + 1) * r) * (Lα1 + Real.log r) :=
            mul_le_mul hmMx this hlm (by positivity)
        _ = _ := by ring
  have hlog2x : |Real.log (2 * x)| ≤ Lx := by
    have h1 : Real.log (2 * α) ≤ Real.log (2 * x) := Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (2 * x) ≤ Real.log (2 * α + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3 : 0 ≤ Real.log (2 * α + 2) := Real.log_nonneg (by linarith)
    rw [hLx]
    rcases abs_cases (Real.log (2 * x)) with ⟨h4, _⟩ | ⟨h4, _⟩
    · rw [h4]; linarith [abs_nonneg (Real.log (2 * α))]
    · rw [h4]; linarith [neg_abs_le (Real.log (2 * α))]
  have hmlog2x : (m : ℝ) * Real.log (2 * x) ≥ -((α + 1) * r * Lx) := by
    have h1 : -Lx ≤ Real.log (2 * x) := by linarith [(abs_le.1 hlog2x).1]
    nlinarith [mul_le_mul_of_nonneg_left h1 hm0, mul_le_mul_of_nonneg_right hmMx hLxnn]
  have hmlogr : (m : ℝ) * Real.log r ≤ (α + 1) * r * Real.log r :=
    mul_le_mul_of_nonneg_right hmMx hlogr
  rw [hAl]
  have hF1 := mul_le_mul_of_nonneg_left hg (sq_nonneg (r : ℝ))
  have hF2 := mul_le_mul_of_nonneg_left hIx (sq_nonneg (r : ℝ))
  have hF2' : (r : ℝ) ^ 2 * (Iu α - 2 * (1 / r) * |c0|) = (r : ℝ) ^ 2 * Iu α - 2 * r * |c0| := by
    field_simp
  have hδr : 0 ≤ δ * (r : ℝ) ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
  have hJ : Jfun α = gJ α + Iu α := rfl
  rw [hJ]
  nlinarith [hF1, hF2, hF2', hδr, hmlogm, hmlog2x, hmlogr, hmMx, hlogr, hr1]

end CatalanCore.Decay
