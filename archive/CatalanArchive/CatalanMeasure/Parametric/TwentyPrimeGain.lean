module
public import CatalanArchive.CatalanMeasure.SparsePrimeGain
@[expose] public section
namespace CatalanMeasure.Parametric
open Real MeasureTheory
open scoped Interval
noncomputable section

def twentyPrimeGain (x : ℝ) : ℝ :=
  3*max (x-22/3) 0-6*max (x-8) 0+3*max (x-26/3) 0

theorem continuous_twentyPrimeGain : Continuous twentyPrimeGain :=by
  unfold twentyPrimeGain
  fun_prop

theorem twentyPrimeGain_left {x : ℝ} (hx : x ≤ 22/3) : twentyPrimeGain x=0 :=by
  simp only [twentyPrimeGain,max_eq_right (show x-22/3 ≤ 0 by linarith),
    max_eq_right (show x-8 ≤ 0 by linarith),max_eq_right (show x-26/3 ≤ 0 by linarith)]
  ring

theorem twentyPrimeGain_ramp {x : ℝ} (hlo : 22/3 ≤ x) (hhi : x ≤ 8) :
    twentyPrimeGain x=3*x-22 :=by
  simp only [twentyPrimeGain,max_eq_left (show 0 ≤ x-22/3 by linarith),
    max_eq_right (show x-8 ≤ 0 by linarith),max_eq_right (show x-26/3 ≤ 0 by linarith)]
  ring

theorem twentyPrimeGain_fall {x : ℝ} (hlo : 8 ≤ x) (hhi : x ≤ 26/3) :
    twentyPrimeGain x=26-3*x :=by
  simp only [twentyPrimeGain,max_eq_left (show 0 ≤ x-22/3 by linarith),
    max_eq_left (show 0 ≤ x-8 by linarith),max_eq_right (show x-26/3 ≤ 0 by linarith)]
  ring

theorem twentyPrimeGain_right {x : ℝ} (hx : 26/3 ≤ x) : twentyPrimeGain x=0 :=by
  simp only [twentyPrimeGain,max_eq_left (show 0 ≤ x-22/3 by linarith),
    max_eq_left (show 0 ≤ x-8 by linarith),max_eq_left (show 0 ≤ x-26/3 by linarith)]
  ring

theorem twentyPrimeGain_bounds (x : ℝ) : 0 ≤ twentyPrimeGain x ∧ twentyPrimeGain x ≤ 2 :=by
  by_cases h0 : x ≤ 22/3
  · rw [twentyPrimeGain_left h0];norm_num
  by_cases h1 : x ≤ 8
  · rw [twentyPrimeGain_ramp (by linarith) h1];constructor <;> linarith
  by_cases h2 : x ≤ 26/3
  · rw [twentyPrimeGain_fall (by linarith) h2];constructor <;> linarith
  rw [twentyPrimeGain_right (by linarith)];norm_num

theorem twentyPrimeGain_pos_window {x : ℝ} (hx : 0<twentyPrimeGain x) :
    22/3<x ∧ x<26/3 :=by
  constructor
  · by_contra hh;rw [twentyPrimeGain_left (by linarith)] at hx;linarith
  · by_contra hh;rw [twentyPrimeGain_right (by linarith)] at hx;linarith

/-- The exact raw area is 4/3; division by the 20-row squared scale gives 1/300. -/
theorem integral_twentyPrimeGain : (∫ x in (1:ℝ)..27,twentyPrimeGain x)=4/3 :=by
  have hi (k : ℝ) : IntervalIntegrable (fun x : ℝ =>max (x-k) 0) volume 1 27 :=
    (by fun_prop : Continuous (fun x : ℝ =>max (x-k) 0)).intervalIntegrable 1 27
  unfold twentyPrimeGain
  rw [intervalIntegral.integral_add ((hi _).const_mul 3 |>.sub ((hi _).const_mul 6))
    ((hi _).const_mul 3),intervalIntegral.integral_sub ((hi _).const_mul 3) ((hi _).const_mul 6)]
  simp only [intervalIntegral.integral_const_mul]
  rw [CatalanMeasure.integral_positive_part 1 27 (22/3) (by norm_num) (by norm_num),
    CatalanMeasure.integral_positive_part 1 27 8 (by norm_num) (by norm_num),
    CatalanMeasure.integral_positive_part 1 27 (26/3) (by norm_num) (by norm_num)]
  norm_num

theorem normalized_integral_twentyPrimeGain :
    (∫ x in (1:ℝ)..27,twentyPrimeGain x)/400=1/300 :=by
  rw [integral_twentyPrimeGain]
  norm_num

end
end CatalanMeasure.Parametric
