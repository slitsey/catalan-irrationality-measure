module

public import CatalanCore.Uniform.Decay.Tools.LogModulusLemmas

@[expose] public section

/-!
# The log-modulus bound, abstract form (lane D, package D5a)

Let `a, b` be two "distance profiles" along a segment `[0, L]` of arclength parameter `s`, with
`a s ≥ |s - x|`, `b s ≥ |s - x'|`, `|a s - b s| ≤ δ`, `|x - x'| ≤ δ` and `0 < δ ≤ 1/4`.  Then

  `∫_0^L |log a - log b| ≤ δ (17 + 14 |log δ| + 3 log (1 + L / (3 δ)))`.

Proof (paper): on the far zone `|s - x| ≥ 3δ` the pointwise bound is
`|log a - log b| ≤ (3/2) δ / |s - x|` (mean value), integrating to `3 δ log(1 + L/(3δ))`;
on the near zone `|s - x| < 3δ` the bound is `1/2 + |log (s-x)| + |log (s-x')|`.
-/

namespace CatalanCore.Uniform.Decay.Assembly

open MeasureTheory Set intervalIntegral CatalanCore.Uniform.Decay.Tools

/-! ### Pointwise bounds -/

theorem log_diff_far {a b x x' s δ : ℝ} (hδ0 : 0 < δ) (hxx' : |x - x'| ≤ δ)
    (ha : |s - x| ≤ a) (hb : |s - x'| ≤ b) (hab : |a - b| ≤ δ) (hw : 3 * δ ≤ |s - x|) :
    |Real.log a - Real.log b| ≤ (3 / 2) * δ / |s - x| := by
  set w := |s - x| with hwdef
  have hw0 : 0 < w := by linarith
  have hsx' : w - δ ≤ |s - x'| := by
    have : |s - x| ≤ |s - x'| + |x - x'| := by
      calc |s - x| = |(s - x') - (x - x')| := by congr 1; ring
        _ ≤ |s - x'| + |x - x'| := abs_sub _ _
    linarith
  have hapos : 0 < a := lt_of_lt_of_le hw0 ha
  have hbpos : 0 < b := by linarith
  have hmin : (2 / 3) * w ≤ min a b := le_min (by linarith) (by linarith)
  refine (abs_log_sub_log_le hapos hbpos).trans ?_
  have hmpos : 0 < (2 / 3) * w := by positivity
  calc |a - b| / min a b ≤ δ / ((2 / 3) * w) :=
        div_le_div₀ hδ0.le hab hmpos hmin
    _ = (3 / 2) * δ / w := by field_simp

theorem log_diff_near {a b x x' s δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) (hsx : s ≠ x)
    (hsx' : s ≠ x') (ha : |s - x| ≤ a) (hb : |s - x'| ≤ b) (hab : |a - b| ≤ δ) :
    |Real.log a - Real.log b| ≤ 1 / 2 + |Real.log (s - x)| + |Real.log (s - x')| := by
  have hw : 0 < |s - x| := abs_pos.2 (sub_ne_zero.2 hsx)
  have hw' : 0 < |s - x'| := abs_pos.2 (sub_ne_zero.2 hsx')
  have hapos : 0 < a := lt_of_lt_of_le hw ha
  have hbpos : 0 < b := lt_of_lt_of_le hw' hb
  have h1 : 0 ≤ |Real.log (s - x)| := abs_nonneg _
  have h2 : 0 ≤ |Real.log (s - x')| := abs_nonneg _
  by_cases hm : 2 * δ ≤ min a b
  · have := abs_log_sub_log_le hapos hbpos
    have h3 : |a - b| / min a b ≤ 1 / 2 := by
      rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hm)]
      nlinarith [abs_nonneg (a - b)]
    linarith
  · push Not at hm
    have hab' := abs_le.1 hab
    have ha3 : a < 3 * δ := by
      rcases min_choice a b with h | h
      · rw [h] at hm; linarith
      · rw [h] at hm; linarith [hab'.1, hab'.2]
    have hb3 : b < 3 * δ := by
      rcases min_choice a b with h | h
      · rw [h] at hm; linarith [hab'.1, hab'.2]
      · rw [h] at hm; linarith
    have hla : |Real.log a| ≤ |Real.log (s - x)| := by
      have ha1 : a < 1 := by linarith
      have hx1 : |s - x| < 1 := lt_of_le_of_lt ha ha1
      have : Real.log |s - x| ≤ Real.log a := Real.log_le_log hw ha
      have h4 : Real.log a ≤ 0 := Real.log_nonpos hapos.le ha1.le
      have h5 : Real.log |s - x| ≤ 0 := Real.log_nonpos hw.le hx1.le
      rw [← Real.log_abs (s - x), abs_of_nonpos h5, abs_of_nonpos h4]
      linarith
    have hlb : |Real.log b| ≤ |Real.log (s - x')| := by
      have hb1 : b < 1 := by linarith
      have hx1 : |s - x'| < 1 := lt_of_le_of_lt hb hb1
      have : Real.log |s - x'| ≤ Real.log b := Real.log_le_log hw' hb
      have h4 : Real.log b ≤ 0 := Real.log_nonpos hbpos.le hb1.le
      have h5 : Real.log |s - x'| ≤ 0 := Real.log_nonpos hw'.le hx1.le
      rw [← Real.log_abs (s - x'), abs_of_nonpos h5, abs_of_nonpos h4]
      linarith
    have := abs_sub (Real.log a) (Real.log b)
    linarith

/-! ### Integral lemmas -/

/-- Right far branch. -/
theorem far_right (x α L : ℝ) (hα : 0 < α) (hL : 0 ≤ L) :
    ∫ s in Ioc 0 L ∩ {s | x + α ≤ s}, (s - x)⁻¹ ≤ Real.log (1 + L / α) := by
  set m : ℝ := max 0 (x + α) with hm
  have hmx : α ≤ m - x := by
    have : x + α ≤ m := le_max_right _ _
    linarith
  have hm0 : 0 ≤ m := le_max_left _ _
  have hpos : ∀ s ∈ Icc m L, 0 < s - x := fun s hs => by linarith [hs.1]
  have hlog0 : 0 ≤ Real.log (1 + L / α) :=
    Real.log_nonneg (by have : 0 ≤ L / α := div_nonneg hL hα.le; linarith)
  by_cases hmL : m ≤ L
  · have hsub : Ioc 0 L ∩ {s | x + α ≤ s} ⊆ Icc m L := by
      intro s ⟨hs1, hs2⟩
      exact ⟨max_le hs1.1.le hs2, hs1.2⟩
    have hint : IntegrableOn (fun s => (s - x)⁻¹) (Icc m L) :=
      (ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
        (fun s hs => (hpos s hs).ne')).integrableOn_Icc
    calc ∫ s in Ioc 0 L ∩ {s | x + α ≤ s}, (s - x)⁻¹
        ≤ ∫ s in Icc m L, (s - x)⁻¹ :=
          setIntegral_mono_set hint
            ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall
              (fun s hs => (inv_pos.2 (hpos s hs)).le)))
            (Filter.Eventually.of_forall hsub)
      _ = ∫ s in m..L, (s - x)⁻¹ := by
          rw [integral_of_le hmL, integral_Icc_eq_integral_Ioc]
      _ = ∫ u in (m - x)..(L - x), u⁻¹ :=
          intervalIntegral.integral_comp_sub_right (fun u : ℝ => u⁻¹) x
      _ ≤ Real.log (1 + (L - m) / (m - x)) :=
          integral_inv_le_log (by linarith) (by linarith) (by linarith)
      _ ≤ Real.log (1 + L / α) := by
          apply Real.log_le_log (by
            have : 0 ≤ (L - m) / (m - x) := div_nonneg (by linarith) (by linarith)
            linarith)
          have : (L - m) / (m - x) ≤ L / α :=
            div_le_div₀ hL (by linarith) hα hmx
          linarith
  · push Not at hmL
    have : Ioc 0 L ∩ {s | x + α ≤ s} ⊆ ∅ := by
      intro s ⟨hs1, hs2⟩
      have : m ≤ s := max_le hs1.1.le hs2
      linarith [hs1.2]
    rw [Set.subset_empty_iff.1 this]
    simpa using hlog0

/-- Left far branch. -/
theorem far_left (x α L : ℝ) (hα : 0 < α) (hL : 0 ≤ L) :
    ∫ s in Ioc 0 L ∩ {s | s ≤ x - α}, (x - s)⁻¹ ≤ Real.log (1 + L / α) := by
  set m : ℝ := min L (x - α) with hm
  have hmx : α ≤ x - m := by
    have : m ≤ x - α := min_le_right _ _
    linarith
  have hmL : m ≤ L := min_le_left _ _
  have hlog0 : 0 ≤ Real.log (1 + L / α) :=
    Real.log_nonneg (by have : 0 ≤ L / α := div_nonneg hL hα.le; linarith)
  by_cases hm0 : 0 ≤ m
  · have hsub : Ioc 0 L ∩ {s | s ≤ x - α} ⊆ Icc 0 m := by
      intro s ⟨hs1, hs2⟩
      exact ⟨hs1.1.le, le_min hs1.2 hs2⟩
    have hpos : ∀ s ∈ Icc 0 m, 0 < x - s := fun s hs => by linarith [hs.2]
    have hint : IntegrableOn (fun s => (x - s)⁻¹) (Icc 0 m) :=
      (ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id)
        (fun s hs => (hpos s hs).ne')).integrableOn_Icc
    calc ∫ s in Ioc 0 L ∩ {s | s ≤ x - α}, (x - s)⁻¹
        ≤ ∫ s in Icc 0 m, (x - s)⁻¹ :=
          setIntegral_mono_set hint
            ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall
              (fun s hs => (inv_pos.2 (hpos s hs)).le)))
            (Filter.Eventually.of_forall hsub)
      _ = ∫ s in (0:ℝ)..m, (x - s)⁻¹ := by
          rw [integral_of_le hm0, integral_Icc_eq_integral_Ioc]
      _ = ∫ u in (x - m)..(x - 0), u⁻¹ :=
          intervalIntegral.integral_comp_sub_left (fun u : ℝ => u⁻¹) x
      _ ≤ Real.log (1 + m / (x - m)) :=
          integral_inv_le_log (by linarith) (by linarith) (by linarith)
      _ ≤ Real.log (1 + L / α) := by
          apply Real.log_le_log (by
            have : 0 ≤ m / (x - m) := div_nonneg hm0 (by linarith)
            linarith)
          have : m / (x - m) ≤ L / α :=
            div_le_div₀ hL hmL hα hmx
          linarith
  · push Not at hm0
    have : Ioc 0 L ∩ {s | s ≤ x - α} ⊆ ∅ := by
      intro s ⟨hs1, hs2⟩
      have : s ≤ m := le_min hs1.2 hs2
      linarith [hs1.1]
    rw [Set.subset_empty_iff.1 this]
    simpa using hlog0

theorem integrableOn_abs_log_shift (c r : ℝ) :
    IntegrableOn (fun s => |Real.log (s - c)|) (Ioc (c - r) (c + r)) := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := -r) (b := r)).abs
  have h2 := h.comp_sub_right c
  have h3 : IntervalIntegrable (fun s : ℝ => |Real.log (s - c)|) volume (c - r) (c + r) := by
    have e1 : -r + c = c - r := by ring
    have e2 : r + c = c + r := by ring
    rw [e1, e2] at h2
    exact h2
  by_cases hr : c - r ≤ c + r
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).1 h3
  · rw [Ioc_eq_empty (by linarith)]
    exact integrableOn_empty

/-- Set integral of `|log (s - c)|` over a subset of `(c - r, c + r]`. -/
theorem setIntegral_abs_log_le {S : Set ℝ} (c r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hS : S ⊆ Ioc (c - r) (c + r)) :
    IntegrableOn (fun s => |Real.log (s - c)|) S ∧
      ∫ s in S, |Real.log (s - c)| ≤ 2 * (r - r * Real.log r) := by
  have hI := integrableOn_abs_log_shift c r
  refine ⟨hI.mono_set hS, ?_⟩
  calc ∫ s in S, |Real.log (s - c)| ≤ ∫ s in Ioc (c - r) (c + r), |Real.log (s - c)| :=
        setIntegral_mono_set hI (Filter.Eventually.of_forall (fun s => abs_nonneg _))
          (Filter.Eventually.of_forall hS)
    _ = ∫ s in (c - r)..(c + r), |Real.log (s - c)| := by
        rw [integral_of_le (by linarith)]
    _ = 2 * (r - r * Real.log r) := integral_abs_log_shift c r hr0 hr1

end CatalanCore.Uniform.Decay.Assembly
