module
public import CatalanArchive.CatalanMeasure.SparsePrimeGain
@[expose] public section
namespace CatalanMeasure
open Real MeasureTheory
open scoped Interval
noncomputable section

def densePrimeGain (x : ℝ) : ℝ :=
  3*max (x-18) 0-3*max (x-58/3) 0-3*max (x-59/3) 0+3*max (x-21) 0

theorem continuous_densePrimeGain : Continuous densePrimeGain :=by unfold densePrimeGain; fun_prop

theorem densePrimeGain_left {x : ℝ} (hx : x ≤ 18) : densePrimeGain x=0 :=by
  simp only [densePrimeGain,max_eq_right (show x-18 ≤ 0 by linarith),
    max_eq_right (show x-58/3 ≤ 0 by linarith),max_eq_right (show x-59/3 ≤ 0 by linarith),
    max_eq_right (show x-21 ≤ 0 by linarith)]
  ring

theorem densePrimeGain_ramp {x : ℝ} (hlo : 18 ≤ x) (hhi : x ≤ 58/3) : densePrimeGain x=3*x-54 :=by
  simp only [densePrimeGain,max_eq_left (show 0 ≤ x-18 by linarith),
    max_eq_right (show x-58/3 ≤ 0 by linarith),max_eq_right (show x-59/3 ≤ 0 by linarith),
    max_eq_right (show x-21 ≤ 0 by linarith)]
  ring

theorem densePrimeGain_plateau {x : ℝ} (hlo : 58/3 ≤ x) (hhi : x ≤ 59/3) : densePrimeGain x=4 :=by
  simp only [densePrimeGain,max_eq_left (show 0 ≤ x-18 by linarith),
    max_eq_left (show 0 ≤ x-58/3 by linarith),max_eq_right (show x-59/3 ≤ 0 by linarith),
    max_eq_right (show x-21 ≤ 0 by linarith)]
  ring

theorem densePrimeGain_fall {x : ℝ} (hlo : 59/3 ≤ x) (hhi : x ≤ 21) : densePrimeGain x=63-3*x :=by
  simp only [densePrimeGain,max_eq_left (show 0 ≤ x-18 by linarith),
    max_eq_left (show 0 ≤ x-58/3 by linarith),max_eq_left (show 0 ≤ x-59/3 by linarith),
    max_eq_right (show x-21 ≤ 0 by linarith)]
  ring

theorem densePrimeGain_right {x : ℝ} (hx : 21 ≤ x) : densePrimeGain x=0 :=by
  simp only [densePrimeGain,max_eq_left (show 0 ≤ x-18 by linarith),
    max_eq_left (show 0 ≤ x-58/3 by linarith),max_eq_left (show 0 ≤ x-59/3 by linarith),
    max_eq_left (show 0 ≤ x-21 by linarith)]
  ring

theorem densePrimeGain_bounds (x : ℝ) :
    0 ≤ densePrimeGain x ∧ densePrimeGain x ≤ 4 ∧ densePrimeGain x ≤ max (63-3*x) 0 :=by
  by_cases h0 : x ≤ 18
  · rw [densePrimeGain_left h0]
    exact ⟨le_rfl,by norm_num,le_max_right _ _⟩
  by_cases h1 : x ≤ 58/3
  · rw [densePrimeGain_ramp (by linarith) h1,max_eq_left (by linarith : 0 ≤ 63-3*x)]
    exact ⟨by linarith,by linarith,by linarith⟩
  by_cases h2 : x ≤ 59/3
  · rw [densePrimeGain_plateau (by linarith) h2,max_eq_left (by linarith : 0 ≤ 63-3*x)]
    exact ⟨by norm_num,le_rfl,by linarith⟩
  by_cases h3 : x ≤ 21
  · rw [densePrimeGain_fall (by linarith) h3,max_eq_left (by linarith : 0 ≤ 63-3*x)]
    exact ⟨by linarith,by linarith,le_rfl⟩
  rw [densePrimeGain_right (by linarith)]
  exact ⟨le_rfl,by norm_num,le_max_right _ _⟩

theorem densePrimeGain_pos_window {x : ℝ} (hx : 0<densePrimeGain x) : 18<x ∧ x<21 :=by
  constructor
  · by_contra hh
    rw [densePrimeGain_left (by linarith)] at hx
    linarith
  · by_contra hh
    rw [densePrimeGain_right (by linarith)] at hx
    linarith

theorem integral_densePrimeGain : (∫ x in (1:ℝ)..65,densePrimeGain x)=20/3 :=by
  have hi (k : ℝ) : IntervalIntegrable (fun x : ℝ =>max (x-k) 0) volume 1 65 :=
    (by fun_prop : Continuous (fun x : ℝ =>max (x-k) 0)).intervalIntegrable 1 65
  unfold densePrimeGain
  rw [intervalIntegral.integral_add ((hi _).const_mul 3 |>.sub ((hi _).const_mul 3) |>.sub ((hi _).const_mul 3))
    ((hi _).const_mul 3),
    intervalIntegral.integral_sub ((hi _).const_mul 3 |>.sub ((hi _).const_mul 3)) ((hi _).const_mul 3),
    intervalIntegral.integral_sub ((hi _).const_mul 3) ((hi _).const_mul 3)]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_positive_part 1 65 18 (by norm_num) (by norm_num),
    integral_positive_part 1 65 (58/3) (by norm_num) (by norm_num),
    integral_positive_part 1 65 (59/3) (by norm_num) (by norm_num),
    integral_positive_part 1 65 21 (by norm_num) (by norm_num)]
  norm_num

end
end CatalanMeasure
