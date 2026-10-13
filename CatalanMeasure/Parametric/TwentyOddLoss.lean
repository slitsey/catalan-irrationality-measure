module
public import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeLoss
@[expose] public section
namespace CatalanMeasure.Parametric
open Set Real
noncomputable section

def twentyOddLoss (x : ℝ) : ℝ :=
  40-2*max (x-10) 0+2*max (x-12) 0-2*max (x-27/2) 0-
    2*max (x-14) 0+max (x-16) 0+2*max (x-24) 0+max (x-27) 0

theorem continuous_twentyOddLoss : Continuous twentyOddLoss :=by
  unfold twentyOddLoss
  fun_prop

theorem twentyOddLoss_segment0 (x : ℝ) (hhi : x ≤ (10:ℝ)) :
    twentyOddLoss x=40-0*x :=by
  rw [twentyOddLoss,
    max_eq_right (show x-(10) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(12) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(27/2) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(14) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(16) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(24) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(27) ≤ (0:ℝ) by linarith only [hhi])]
  ring

theorem twentyOddLoss_segment1 (x : ℝ) (hlo : (10:ℝ) ≤ x) (hhi : x ≤ (12:ℝ)) :
    twentyOddLoss x=60-2*x :=by
  rw [twentyOddLoss,
    max_eq_left (show (0:ℝ) ≤ x-(10) by linarith only [hlo]),
    max_eq_right (show x-(12) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(27/2) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(14) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(16) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(24) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(27) ≤ (0:ℝ) by linarith only [hhi])]
  ring

theorem twentyOddLoss_segment2 (x : ℝ) (hlo : (12:ℝ) ≤ x) (hhi : x ≤ (27/2:ℝ)) :
    twentyOddLoss x=36-0*x :=by
  rw [twentyOddLoss,
    max_eq_left (show (0:ℝ) ≤ x-(10) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(12) by linarith only [hlo]),
    max_eq_right (show x-(27/2) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(14) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(16) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(24) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(27) ≤ (0:ℝ) by linarith only [hhi])]
  ring

theorem twentyOddLoss_segment3 (x : ℝ) (hlo : (27/2:ℝ) ≤ x) (hhi : x ≤ (14:ℝ)) :
    twentyOddLoss x=63-2*x :=by
  rw [twentyOddLoss,
    max_eq_left (show (0:ℝ) ≤ x-(10) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(12) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(27/2) by linarith only [hlo]),
    max_eq_right (show x-(14) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(16) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(24) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(27) ≤ (0:ℝ) by linarith only [hhi])]
  ring

theorem twentyOddLoss_segment4 (x : ℝ) (hlo : (14:ℝ) ≤ x) (hhi : x ≤ (16:ℝ)) :
    twentyOddLoss x=91-4*x :=by
  rw [twentyOddLoss,
    max_eq_left (show (0:ℝ) ≤ x-(10) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(12) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(27/2) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(14) by linarith only [hlo]),
    max_eq_right (show x-(16) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(24) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(27) ≤ (0:ℝ) by linarith only [hhi])]
  ring

theorem twentyOddLoss_segment5 (x : ℝ) (hlo : (16:ℝ) ≤ x) (hhi : x ≤ (24:ℝ)) :
    twentyOddLoss x=75-3*x :=by
  rw [twentyOddLoss,
    max_eq_left (show (0:ℝ) ≤ x-(10) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(12) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(27/2) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(14) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(16) by linarith only [hlo]),
    max_eq_right (show x-(24) ≤ (0:ℝ) by linarith only [hhi]),
    max_eq_right (show x-(27) ≤ (0:ℝ) by linarith only [hhi])]
  ring

theorem twentyOddLoss_segment6 (x : ℝ) (hlo : (24:ℝ) ≤ x) (hhi : x ≤ (27:ℝ)) :
    twentyOddLoss x=27-1*x :=by
  rw [twentyOddLoss,
    max_eq_left (show (0:ℝ) ≤ x-(10) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(12) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(27/2) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(14) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(16) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(24) by linarith only [hlo]),
    max_eq_right (show x-(27) ≤ (0:ℝ) by linarith only [hhi])]
  ring

theorem twentyOddLoss_segment7 (x : ℝ) (hlo : (27:ℝ) ≤ x) :
    twentyOddLoss x=0-0*x :=by
  rw [twentyOddLoss,
    max_eq_left (show (0:ℝ) ≤ x-(10) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(12) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(27/2) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(14) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(16) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(24) by linarith only [hlo]),
    max_eq_left (show (0:ℝ) ≤ x-(27) by linarith only [hlo])]
  ring

private theorem twenty_loss_integral_affine (a b c m : ℝ) :
    (∫ x in a..b,c-m*x)=c*(b-a)-m*((b^2-a^2)/2) :=by
  rw [intervalIntegral.integral_sub
    (f :=fun _ : ℝ =>c) (g :=fun x : ℝ =>m*x)
    (continuous_const.intervalIntegrable a b)
    ((continuous_const.mul continuous_id).intervalIntegrable a b)]
  rw [intervalIntegral.integral_const_mul m (fun x : ℝ =>x)]
  simp only [intervalIntegral.integral_const,integral_id,smul_eq_mul]
  ring

theorem integral_twentyOddLoss_segment0 :
    (∫ x in (0:ℝ)..(10),twentyOddLoss x)=400 :=by
  calc
    _ = ∫ x in (0:ℝ)..(10),40-0*x :=by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact twentyOddLoss_segment0 x hx.2
    _ = _ :=by rw [twenty_loss_integral_affine];norm_num

theorem integral_twentyOddLoss_segment1 :
    (∫ x in (10:ℝ)..(12),twentyOddLoss x)=76 :=by
  calc
    _ = ∫ x in (10:ℝ)..(12),60-2*x :=by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact twentyOddLoss_segment1 x hx.1 hx.2
    _ = _ :=by rw [twenty_loss_integral_affine];norm_num

theorem integral_twentyOddLoss_segment2 :
    (∫ x in (12:ℝ)..(27/2),twentyOddLoss x)=54 :=by
  calc
    _ = ∫ x in (12:ℝ)..(27/2),36-0*x :=by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact twentyOddLoss_segment2 x hx.1 hx.2
    _ = _ :=by rw [twenty_loss_integral_affine];norm_num

theorem integral_twentyOddLoss_segment3 :
    (∫ x in (27/2:ℝ)..(14),twentyOddLoss x)=71/4 :=by
  calc
    _ = ∫ x in (27/2:ℝ)..(14),63-2*x :=by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact twentyOddLoss_segment3 x hx.1 hx.2
    _ = _ :=by rw [twenty_loss_integral_affine];norm_num

theorem integral_twentyOddLoss_segment4 :
    (∫ x in (14:ℝ)..(16),twentyOddLoss x)=62 :=by
  calc
    _ = ∫ x in (14:ℝ)..(16),91-4*x :=by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact twentyOddLoss_segment4 x hx.1 hx.2
    _ = _ :=by rw [twenty_loss_integral_affine];norm_num

theorem integral_twentyOddLoss_segment5 :
    (∫ x in (16:ℝ)..(24),twentyOddLoss x)=120 :=by
  calc
    _ = ∫ x in (16:ℝ)..(24),75-3*x :=by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact twentyOddLoss_segment5 x hx.1 hx.2
    _ = _ :=by rw [twenty_loss_integral_affine];norm_num

theorem integral_twentyOddLoss_segment6 :
    (∫ x in (24:ℝ)..(27),twentyOddLoss x)=9/2 :=by
  calc
    _ = ∫ x in (24:ℝ)..(27),27-1*x :=by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact twentyOddLoss_segment6 x hx.1 hx.2
    _ = _ :=by rw [twenty_loss_integral_affine];norm_num

theorem integral_twentyOddLoss :
    (∫ x in (0:ℝ)..27,twentyOddLoss x)=2937/4 :=by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_twentyOddLoss.intervalIntegrable (0) (10))
    (continuous_twentyOddLoss.intervalIntegrable (10) 27)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_twentyOddLoss.intervalIntegrable (10) (12))
    (continuous_twentyOddLoss.intervalIntegrable (12) 27)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_twentyOddLoss.intervalIntegrable (12) (27/2))
    (continuous_twentyOddLoss.intervalIntegrable (27/2) 27)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_twentyOddLoss.intervalIntegrable (27/2) (14))
    (continuous_twentyOddLoss.intervalIntegrable (14) 27)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_twentyOddLoss.intervalIntegrable (14) (16))
    (continuous_twentyOddLoss.intervalIntegrable (16) 27)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_twentyOddLoss.intervalIntegrable (16) (24))
    (continuous_twentyOddLoss.intervalIntegrable (24) 27)]
  rw [integral_twentyOddLoss_segment0,integral_twentyOddLoss_segment1,integral_twentyOddLoss_segment2,integral_twentyOddLoss_segment3,integral_twentyOddLoss_segment4,integral_twentyOddLoss_segment5,integral_twentyOddLoss_segment6]
  norm_num

theorem integral_twentyOddLoss_normalized :
    (∫ x in (0:ℝ)..27,twentyOddLoss x)/400=2937/1600 :=by
  rw [integral_twentyOddLoss]
  norm_num

end
end CatalanMeasure.Parametric
