module
public import CatalanMeasure.Parametric.RadiusQuadrature
public import CatalanMeasure.Parametric.TwentyCircle
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Polynomial.Chebyshev Finset
noncomputable section
theorem twenty_norm_restricted_filtered_basis_le (N : ℕ) (a : Fin (18*N)) (t : ℂ)
    (ht : ‖t‖=(TwentyCircle.twentyRadius:ℝ)) :
    ‖((OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (18*N)) a *
      (1-X)^(2*N)).map (algebraMap ℝ ℂ)).eval t‖ ≤
      500*(TwentyCircle.twentyCircleK:ℝ)^N := by
  have hr : 1<(TwentyCircle.twentyRadius:ℝ) := by norm_num [TwentyCircle.twentyRadius]
  have hJ : (1:ℝ) ≤ (18*N:ℕ) := by exact_mod_cast (show 1≤18*N by have := a.isLt; omega)
  set s : ℝ := ‖t+1‖ with hs
  have hs0 : 0≤s := norm_nonneg _
  have hslow : (TwentyCircle.twentyRadius:ℝ)-1 ≤ s := by
    have hh := norm_sub_norm_le t (-1:ℂ)
    simpa [ht,hs] using hh
  have hs2 : s≤(TwentyCircle.twentyRadius:ℝ)+1 := by
    have hh := norm_add_le t 1
    simpa [ht,hs] using hh
  have hpar : ‖1-t‖^2 = 2*((TwentyCircle.twentyRadius:ℝ)^2+1)-s^2 := by
    have hh := parallelogram_law_with_norm ℝ t (1:ℂ)
    rw [ht,norm_one,← hs,norm_sub_rev] at hh
    nlinarith
  have hz1 : ‖(2*t+1)-1‖=2*(TwentyCircle.twentyRadius:ℝ) := by
    rw [show (2*t+1)-1=2*t by ring,norm_mul,ht]
    norm_num
  have hz2 : ‖(2*t+1)+1‖=2*s := by
    rw [show (2*t+1)+1=2*(t+1) by ring,norm_mul,← hs]
    norm_num
  set B := (TwentyCircle.twentyRadius:ℝ)+s+Real.sqrt (((TwentyCircle.twentyRadius:ℝ)+s)^2-1) with hB
  have hB0 : 0≤B := by
    dsimp [B]
    have hh : (0:ℝ)≤TwentyCircle.twentyRadius := by norm_num [TwentyCircle.twentyRadius]
    positivity
  have hT := CatalanMeasure.norm_T_eval_le (18*N) (2*t+1)
  rw [hz1,hz2,show (2*(TwentyCircle.twentyRadius:ℝ)+2*s)/2=(TwentyCircle.twentyRadius:ℝ)+s by ring,
    ← hB] at hT
  have hKfull := TwentyCircle.twentyCircle_ineq hslow hs2
  rw [← hB,← hpar] at hKfull
  have hrad : 1≤(TwentyCircle.twentyRadius:ℝ)^4 := one_le_pow₀ hr.le
  have hK : B^18*(‖1-t‖^2)^1 ≤ (TwentyCircle.twentyCircleK:ℝ) := by
    exact (le_mul_of_one_le_right (by positivity) hrad).trans hKfull
  have hl := norm_quadBasis_eval_radius_le a t hr ht
  have hl' : ‖((OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (18*N)) a).map
      (algebraMap ℝ ℂ)).eval t‖ ≤ 500*‖(T ℂ ((18*N:ℕ):ℤ)).eval (2*t+1)‖ := by
    apply hl.trans
    have hd : (0:ℝ)<2*(18*N:ℕ)*((TwentyCircle.twentyRadius:ℝ)-1) := by
      exact mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hJ)) (sub_pos.mpr hr)
    apply (div_le_iff₀ hd).mpr
    have hh : (500:ℝ)*(2*(18*N:ℕ)*((TwentyCircle.twentyRadius:ℝ)-1)) = (18*N:ℕ) := by
      norm_num [TwentyCircle.twentyRadius]
      ring
    calc
      _ ≤ (18*N:ℕ)*‖(T ℂ ((18*N:ℕ):ℤ)).eval (2*t+1)‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hJ
      _ = (500*‖(T ℂ ((18*N:ℕ):ℤ)).eval (2*t+1)‖) *
          (2*(18*N:ℕ)*((TwentyCircle.twentyRadius:ℝ)-1)) := by
            nth_rw 1 [← hh]
            ring
  rw [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_one,
    Polynomial.map_X,eval_mul,eval_pow,eval_sub,eval_one,eval_X,norm_mul,norm_pow]
  have e1 : ‖1-t‖^(2*N)=((‖1-t‖^2)^1)^N := by
    rw [← pow_mul,← pow_mul]
    congr 1
    ring
  have e2 : B^(18*N)=(B^18)^N := pow_mul B 18 N
  calc
    _ ≤ (500*B^(18*N))*‖1-t‖^(2*N) := by
        exact mul_le_mul_of_nonneg_right
          (hl'.trans (mul_le_mul_of_nonneg_left hT (by norm_num))) (by positivity)
    _ = 500*(B^18*(‖1-t‖^2)^1)^N := by rw [e1,e2,mul_pow,mul_assoc]
    _ ≤ 500*(TwentyCircle.twentyCircleK:ℝ)^N := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hK N) (by norm_num)

end
end CatalanMeasure.Parametric
