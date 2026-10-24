module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyPrimeGain
@[expose] public section
namespace CatalanMeasure.Parametric
open Real MeasureTheory
open scoped Interval
noncomputable section

/-- The audited asymmetric full-frame secondary-content profile. -/
def secondaryTentProfile (x : ℝ) : ℝ :=
  max 0 (min ((9*x-52)/2) ((44-7*x)/2))

theorem continuous_secondaryTentProfile : Continuous secondaryTentProfile := by
  unfold secondaryTentProfile
  fun_prop

theorem secondaryTentProfile_nonneg (x : ℝ) : 0 ≤ secondaryTentProfile x :=
  le_max_left _ _

theorem secondaryTentProfile_left {x : ℝ} (hx : x ≤ 52/9) :
    secondaryTentProfile x = 0 := by
  unfold secondaryTentProfile
  exact max_eq_left ((min_le_left _ _).trans (by linarith))

theorem secondaryTentProfile_right {x : ℝ} (hx : 44/7 ≤ x) :
    secondaryTentProfile x = 0 := by
  unfold secondaryTentProfile
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem secondaryTentProfile_rise {x : ℝ} (ha : 52/9 ≤ x) (hb : x ≤ 6) :
    secondaryTentProfile x = (9*x-52)/2 := by
  unfold secondaryTentProfile
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

theorem secondaryTentProfile_fall {x : ℝ} (ha : 6 ≤ x) (hb : x ≤ 44/7) :
    secondaryTentProfile x = (44-7*x)/2 := by
  unfold secondaryTentProfile
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

theorem secondaryTentProfile_positive_parts (x : ℝ) :
    secondaryTentProfile x = (9/2)*max (x-52/9) 0 -
      8*max (x-6) 0 + (7/2)*max (x-44/7) 0 := by
  by_cases h0 : x ≤ 52/9
  · rw [secondaryTentProfile_left h0]
    rw [max_eq_right (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith)]
    ring
  by_cases h1 : x ≤ 6
  · rw [secondaryTentProfile_rise (by linarith) h1]
    rw [max_eq_left (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith)]
    ring
  by_cases h2 : x ≤ 44/7
  · rw [secondaryTentProfile_fall (by linarith) h2]
    rw [max_eq_left (by linarith), max_eq_left (by linarith),
      max_eq_right (by linarith)]
    ring
  rw [secondaryTentProfile_right (by linarith)]
  rw [max_eq_left (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith)]
  ring

theorem integral_secondaryTentProfile :
    (∫ x in (1:ℝ)..7, secondaryTentProfile x) = 16/63 := by
  have hi (k : ℝ) : IntervalIntegrable (fun x : ℝ => max (x-k) 0) volume 1 7 :=
    (by fun_prop : Continuous (fun x : ℝ => max (x-k) 0)).intervalIntegrable 1 7
  simp_rw [secondaryTentProfile_positive_parts]
  rw [intervalIntegral.integral_add (((hi _).const_mul (9/2)).sub ((hi _).const_mul 8))
    ((hi _).const_mul (7/2)),
    intervalIntegral.integral_sub ((hi _).const_mul (9/2)) ((hi _).const_mul 8)]
  simp only [intervalIntegral.integral_const_mul]
  rw [CatalanMeasure.integral_positive_part 1 7 (52/9) (by norm_num) (by norm_num),
    CatalanMeasure.integral_positive_part 1 7 6 (by norm_num) (by norm_num),
    CatalanMeasure.integral_positive_part 1 7 (44/7) (by norm_num) (by norm_num)]
  norm_num

end
end CatalanMeasure.Parametric
