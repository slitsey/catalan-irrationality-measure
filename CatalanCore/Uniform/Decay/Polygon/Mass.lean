module

public import CatalanCore.Uniform.Decay.Polygon.Bounds

@[expose] public section

/-!
# Residual mass of the polygon parameter measure (Part 2, Lemma `allJ`, residual measure)

For every `c > 0`, the residual density `e^{-c |Im γ(u)|} |γ'(u)|` of the (upper) polygon is
integrable on `(0, ∞)` and
`∫ e^{-c|Im γ|} |γ'| ≤ (traversed length of the finite edges) + |d| / (c Im d)`.
Multiplicities are counted (`chainLen` sums the edge lengths with repetition).  The lower path has
the same density (`conjL_conj_path`, `conjL_conj_der`).
-/

open MeasureTheory Set Filter Topology

namespace CatalanCore.Uniform.Decay.Polygon

/-- Traversed length of the finite chain `a → l`. -/
noncomputable def chainLen : ℂ → List ℂ → ℝ
  | _, [] => 0
  | a, b :: l => ‖b - a‖ + chainLen b l

theorem setIntegral_Ioi_shift_real (g : ℝ → ℝ) (c : ℝ) :
    ∫ u in Ioi c, g (u - c) = ∫ u in Ioi (0 : ℝ), g u := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have e : (Ioi c).indicator (fun u => g (u - c)) = fun u => (Ioi (0 : ℝ)).indicator g (u - c) := by
    funext u
    by_cases h : c < u
    · rw [indicator_of_mem (show u ∈ Ioi c from h),
        indicator_of_mem (show u - c ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith)]
    · rw [indicator_of_notMem (show u ∉ Ioi c from h),
        indicator_of_notMem (show u - c ∉ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith)]
  rw [e]
  exact integral_sub_right_eq_self _ c

theorem integrableOn_Ioi_shift_real {g : ℝ → ℝ} (c : ℝ) (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun u => g (u - c)) (Ioi c) := by
  rw [← integrable_indicator_iff measurableSet_Ioi] at hg ⊢
  have e : (Ioi c).indicator (fun u => g (u - c)) = fun u => (Ioi (0 : ℝ)).indicator g (u - c) := by
    funext u
    by_cases h : c < u
    · rw [indicator_of_mem (show u ∈ Ioi c from h),
        indicator_of_mem (show u - c ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith)]
    · rw [indicator_of_notMem (show u ∉ Ioi c from h),
        indicator_of_notMem (show u - c ∉ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith)]
  rw [e]
  exact hg.comp_sub_right c

/-- **Residual mass of the polygon.** -/
theorem pathMass {c : ℝ} (hc : 0 < c) {d : ℂ} (hd : 0 < d.im) :
    ∀ (l : List ℂ) (a : ℂ), 0 ≤ ((a :: l).getLast (List.cons_ne_nil a l)).im →
      IntegrableOn (fun u => Real.exp (-(c * |(pathPt d a l u).im|)) * ‖pathDer d a l u‖) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), Real.exp (-(c * |(pathPt d a l u).im|)) * ‖pathDer d a l u‖
        ≤ chainLen a l + ‖d‖ / (c * d.im)
  | [], a, ha => by
    have ha' : 0 ≤ a.im := by simpa using ha
    set b := c * d.im with hb
    have hb0 : 0 < b := mul_pos hc hd
    have hbound : ∀ u ∈ Ioi (0 : ℝ),
        Real.exp (-(c * |(pathPt d a [] u).im|)) * ‖pathDer d a [] u‖
          ≤ ‖d‖ * Real.exp (-b * u) := by
      intro u hu
      have hu : 0 < u := hu
      simp only [pathPt, pathDer]
      rw [im_ray, abs_of_nonneg (by nlinarith), mul_comm]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
      rw [hb]; nlinarith
    have hI : IntegrableOn (fun u : ℝ => ‖d‖ * Real.exp (-b * u)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0).const_mul _
    have hcont : Continuous (fun u : ℝ => Real.exp (-(c * |(pathPt d a [] u).im|)) * ‖pathDer d a [] u‖) := by
      simp only [pathPt, pathDer]; fun_prop
    have hG : IntegrableOn (fun u => Real.exp (-(c * |(pathPt d a [] u).im|)) * ‖pathDer d a [] u‖)
        (Ioi 0) := by
      refine hI.mono' hcont.aestronglyMeasurable.restrict ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      rw [Real.norm_of_nonneg (by positivity)]; exact hbound u hu
    refine ⟨hG, ?_⟩
    calc ∫ u in Ioi (0 : ℝ), Real.exp (-(c * |(pathPt d a [] u).im|)) * ‖pathDer d a [] u‖
        ≤ ∫ u in Ioi (0 : ℝ), ‖d‖ * Real.exp (-b * u) :=
          setIntegral_mono_on hG hI measurableSet_Ioi hbound
      _ = ‖d‖ / b := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
          simp; field_simp
      _ = chainLen a [] + ‖d‖ / (c * d.im) := by simp [chainLen, hb]
  | b :: l, a, ha => by
    have ha' : 0 ≤ ((b :: l).getLast (List.cons_ne_nil b l)).im := by
      simpa [List.getLast_cons_cons] using ha
    obtain ⟨hI, hE⟩ := pathMass hc hd l b ha'
    set G := fun u => Real.exp (-(c * |(pathPt d a (b :: l) u).im|)) * ‖pathDer d a (b :: l) u‖
      with hG
    set h := fun u : ℝ => Real.exp (-(c * |(a + (u : ℂ) * (b - a)).im|)) * ‖b - a‖ with hh
    have hcont : Continuous h := by simp only [hh]; fun_prop
    have eq1 : EqOn G h (Icc 0 1) := by
      intro u hu
      simp only [hG, hh, pathPt, pathDer, if_pos hu.2]
    have eq2 : EqOn G (fun u => Real.exp (-(c * |(pathPt d b l (u - 1)).im|))
        * ‖pathDer d b l (u - 1)‖) (Ioi 1) := by
      intro u hu
      have : ¬ u ≤ 1 := not_le.2 hu
      simp only [hG, pathPt, pathDer, if_neg this]
    have i1 : IntegrableOn G (Ioc 0 1) :=
      ((hcont.continuousOn.integrableOn_Icc).congr_fun eq1.symm measurableSet_Icc).mono_set
        Ioc_subset_Icc_self
    have i2 : IntegrableOn G (Ioi 1) :=
      (integrableOn_Ioi_shift_real
        (g := fun u => Real.exp (-(c * |(pathPt d b l u).im|)) * ‖pathDer d b l u‖) 1 hI).congr_fun
        eq2.symm measurableSet_Ioi
    have hU : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
    refine ⟨by rw [hU]; exact i1.union i2, ?_⟩
    rw [hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2,
      setIntegral_congr_fun measurableSet_Ioi eq2,
      setIntegral_Ioi_shift_real (fun u => Real.exp (-(c * |(pathPt d b l u).im|))
        * ‖pathDer d b l u‖) 1]
    have h1 : ∫ u in Ioc (0 : ℝ) 1, G u ≤ ‖b - a‖ := by
      rw [← intervalIntegral.integral_of_le zero_le_one]
      have hii : IntervalIntegrable G volume 0 1 :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 i1
      calc ∫ u in (0 : ℝ)..1, G u ≤ ∫ u in (0 : ℝ)..1, ‖b - a‖ :=
            intervalIntegral.integral_mono_on zero_le_one hii intervalIntegrable_const
              (fun u hu => by
                rw [eq1 hu]; simp only [hh]
                have : Real.exp (-(c * |(a + (u : ℂ) * (b - a)).im|)) ≤ 1 := by
                  rw [Real.exp_le_one_iff]; have := abs_nonneg (a + (u : ℂ) * (b - a)).im
                  nlinarith
                nlinarith [norm_nonneg (b - a)])
        _ = ‖b - a‖ := by simp
    have : chainLen a (b :: l) = ‖b - a‖ + chainLen b l := rfl
    rw [this]
    linarith

end CatalanCore.Uniform.Decay.Polygon
