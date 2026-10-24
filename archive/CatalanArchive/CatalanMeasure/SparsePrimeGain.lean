module
public import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeLoss
@[expose] public section
namespace CatalanMeasure
open Real MeasureTheory Set
open scoped Interval
noncomputable section

/-- A continuous saving below the certified sparse mode count. -/
def sparsePrimeGain (x : ℝ) : ℝ :=
  4000*max (x-58/3) 0-4000*max (x-58003/3000) 0-
    3*max (x-59/3) 0+3*max (x-21) 0

theorem continuous_sparsePrimeGain : Continuous sparsePrimeGain :=by
  unfold sparsePrimeGain
  fun_prop

theorem sparsePrimeGain_left {x : ℝ} (hx : x ≤ 58/3) : sparsePrimeGain x=0 :=by
  simp only [sparsePrimeGain,max_eq_right (show x-58/3 ≤ 0 by linarith),
    max_eq_right (show x-58003/3000 ≤ 0 by linarith),
    max_eq_right (show x-59/3 ≤ 0 by linarith),max_eq_right (show x-21 ≤ 0 by linarith)]
  ring

theorem sparsePrimeGain_ramp {x : ℝ} (hlo : 58/3 ≤ x) (hhi : x ≤ 58003/3000) :
    sparsePrimeGain x=4000*(x-58/3) :=by
  simp only [sparsePrimeGain,max_eq_left (show 0 ≤ x-58/3 by linarith),
    max_eq_right (show x-58003/3000 ≤ 0 by linarith),
    max_eq_right (show x-59/3 ≤ 0 by linarith),max_eq_right (show x-21 ≤ 0 by linarith)]
  ring

theorem sparsePrimeGain_plateau {x : ℝ} (hlo : 58003/3000 ≤ x) (hhi : x ≤ 59/3) :
    sparsePrimeGain x=4 :=by
  simp only [sparsePrimeGain,max_eq_left (show 0 ≤ x-58/3 by linarith),
    max_eq_left (show 0 ≤ x-58003/3000 by linarith),
    max_eq_right (show x-59/3 ≤ 0 by linarith),max_eq_right (show x-21 ≤ 0 by linarith)]
  ring

theorem sparsePrimeGain_fall {x : ℝ} (hlo : 59/3 ≤ x) (hhi : x ≤ 21) :
    sparsePrimeGain x=63-3*x :=by
  simp only [sparsePrimeGain,max_eq_left (show 0 ≤ x-58/3 by linarith),
    max_eq_left (show 0 ≤ x-58003/3000 by linarith),
    max_eq_left (show 0 ≤ x-59/3 by linarith),max_eq_right (show x-21 ≤ 0 by linarith)]
  ring

theorem sparsePrimeGain_right {x : ℝ} (hx : 21 ≤ x) : sparsePrimeGain x=0 :=by
  simp only [sparsePrimeGain,max_eq_left (show 0 ≤ x-58/3 by linarith),
    max_eq_left (show 0 ≤ x-58003/3000 by linarith),
    max_eq_left (show 0 ≤ x-59/3 by linarith),max_eq_left (show 0 ≤ x-21 by linarith)]
  ring

theorem sparsePrimeGain_bounds (x : ℝ) :
    0 ≤ sparsePrimeGain x ∧ sparsePrimeGain x ≤ 4 ∧ sparsePrimeGain x ≤ max (63-3*x) 0 :=by
  by_cases h0 : x ≤ 58/3
  · rw [sparsePrimeGain_left h0]
    exact ⟨le_rfl,by norm_num,le_max_right _ _⟩
  by_cases h1 : x ≤ 58003/3000
  · rw [sparsePrimeGain_ramp (by linarith) h1]
    rw [max_eq_left (by linarith : 0 ≤ 63-3*x)]
    constructor <;> [linarith;constructor <;> linarith]
  by_cases h2 : x ≤ 59/3
  · rw [sparsePrimeGain_plateau (by linarith) h2]
    rw [max_eq_left (by linarith : 0 ≤ 63-3*x)]
    exact ⟨by norm_num,le_rfl,by linarith⟩
  by_cases h3 : x ≤ 21
  · rw [sparsePrimeGain_fall (by linarith) h3]
    rw [max_eq_left (by linarith : 0 ≤ 63-3*x)]
    exact ⟨by linarith,by linarith,le_rfl⟩
  rw [sparsePrimeGain_right (by linarith)]
  exact ⟨le_rfl,by norm_num,le_max_right _ _⟩

theorem sparsePrimeGain_pos_window {x : ℝ} (hx : 0<sparsePrimeGain x) : 58/3<x ∧ x<21 :=by
  constructor
  · by_contra hh
    rw [sparsePrimeGain_left (by linarith)] at hx
    linarith
  · by_contra hh
    rw [sparsePrimeGain_right (by linarith)] at hx
    linarith

theorem integral_positive_part (a b k : ℝ) (ha : a ≤ k) (hb : k ≤ b) :
    (∫ x in a..b,max (x-k) 0)=(b-k)^2/2 :=by
  have hc : Continuous (fun x : ℝ =>max (x-k) 0) :=by fun_prop
  have hleft : (∫ x in a..k,max (x-k) 0)=0 :=by
    calc
      _ = ∫ x in a..k,(0:ℝ) :=by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le ha] at hx
        exact max_eq_right (by linarith [hx.2])
      _ = 0 :=by simp
  have hright : (∫ x in k..b,max (x-k) 0)=(b-k)^2/2 :=by
    calc
      _ = ∫ x in k..b,x-k :=by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hb] at hx
        exact max_eq_left (by linarith [hx.1])
      _ = _ :=by
        rw [intervalIntegral.integral_sub (f:=fun x : ℝ =>x) (g:=fun _ : ℝ =>k)
          (continuous_id.intervalIntegrable k b)
          (continuous_const.intervalIntegrable k b)]
        simp only [integral_id,intervalIntegral.integral_const,smul_eq_mul]
        ring
  have hh :=intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hc.intervalIntegrable a k) (hc.intervalIntegrable k b)
  rw [hleft,hright,zero_add] at hh
  exact hh.symm

theorem integral_sparsePrimeGain : (∫ x in (1:ℝ)..65,sparsePrimeGain x)=1999/500 :=by
  have hi (k : ℝ) : IntervalIntegrable (fun x : ℝ => max (x-k) 0) volume 1 65 :=by
    exact (by fun_prop : Continuous (fun x : ℝ =>max (x-k) 0)).intervalIntegrable 1 65
  unfold sparsePrimeGain
  rw [intervalIntegral.integral_add ((hi _).const_mul 4000 |>.sub ((hi _).const_mul 4000) |>.sub ((hi _).const_mul 3))
    ((hi _).const_mul 3),
    intervalIntegral.integral_sub ((hi _).const_mul 4000 |>.sub ((hi _).const_mul 4000)) ((hi _).const_mul 3),
    intervalIntegral.integral_sub ((hi _).const_mul 4000) ((hi _).const_mul 4000)]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_positive_part 1 65 (58/3) (by norm_num) (by norm_num),
    integral_positive_part 1 65 (58003/3000) (by norm_num) (by norm_num),
    integral_positive_part 1 65 (59/3) (by norm_num) (by norm_num),
    integral_positive_part 1 65 21 (by norm_num) (by norm_num)]
  norm_num

end
end CatalanMeasure
