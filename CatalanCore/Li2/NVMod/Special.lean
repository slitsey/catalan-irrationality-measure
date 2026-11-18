module
public import CatalanCore.Li2.NV.Constants
public import Mathlib.Tactic.ComputeDegree
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section
private theorem degree_linear (a b : ℚ) : degree (C a*X+C b) ≤ 1 := by
  exact (degree_add_le _ _).trans (max_le (degree_C_mul_X_le a) (degree_C_le.trans (by norm_num)))
private theorem degree_quadratic (a b c : ℚ) : degree (C a*X^2+C b*X+C c) ≤ 2 := by
  exact (degree_add_le _ _).trans (max_le
    ((degree_add_le _ _).trans (max_le (degree_C_mul_X_pow_le 2 a)
      ((degree_C_mul_X_le b).trans (by norm_num))))
    (degree_C_le.trans (by norm_num)))
private theorem num_13 : weightNum ⟨.V,1,3,2⟩=(X^2:ℚ[X]) := by norm_num [weightNum]
private theorem den_13 : weightDen ⟨.V,1,3,2⟩=((X+C (1:ℚ))*(X+C (2:ℚ)):ℚ[X]) := by
  norm_num [weightDen,poleSet,Finset.prod_Ico_succ_top,Finset.prod_range_succ,map_ofNat]
private theorem quotient_13_0 : polyPart ⟨.V,1,3,2⟩ (X^0)=(1:ℚ[X]) := by
  rw [polyPart,num_13,den_13]
  apply (div_modByMonic_unique (1) (C (-3:ℚ)*X^1+C (-2:ℚ)*X^0) ?_ ⟨by norm_num only [map_ofNat,map_neg,map_zero,map_one];ring,?_⟩).1
  · repeat' apply Monic.mul
    all_goals exact monic_X_add_C _
  · have hr : degree (C (-3:ℚ)*X^1+C (-2:ℚ)*X^0:ℚ[X]) ≤ 1 := by
      simpa only [pow_zero,mul_one,pow_one] using (degree_linear (-3:ℚ) (-2:ℚ))
    apply hr.trans_lt
    simp only [degree_mul,degree_X_add_C]
    norm_num
private theorem quotient_13_1 : polyPart ⟨.V,1,3,2⟩ (X^1)=(X-3:ℚ[X]) := by
  rw [polyPart,num_13,den_13]
  apply (div_modByMonic_unique (X-3) (C (7:ℚ)*X^1+C (6:ℚ)*X^0) ?_ ⟨by norm_num only [map_ofNat,map_neg,map_zero,map_one];ring,?_⟩).1
  · repeat' apply Monic.mul
    all_goals exact monic_X_add_C _
  · have hr : degree (C (7:ℚ)*X^1+C (6:ℚ)*X^0:ℚ[X]) ≤ 1 := by
      simpa only [pow_zero,mul_one,pow_one] using (degree_linear (7:ℚ) (6:ℚ))
    apply hr.trans_lt
    simp only [degree_mul,degree_X_add_C]
    norm_num
private theorem quotient_13_2 : polyPart ⟨.V,1,3,2⟩ (X^2)=(X^2-3*X+7:ℚ[X]) := by
  rw [polyPart,num_13,den_13]
  apply (div_modByMonic_unique (X^2-3*X+7) (C (-15:ℚ)*X^1+C (-14:ℚ)*X^0) ?_ ⟨by norm_num only [map_ofNat,map_neg,map_zero,map_one];ring,?_⟩).1
  · repeat' apply Monic.mul
    all_goals exact monic_X_add_C _
  · have hr : degree (C (-15:ℚ)*X^1+C (-14:ℚ)*X^0:ℚ[X]) ≤ 1 := by
      simpa only [pow_zero,mul_one,pow_one] using (degree_linear (-15:ℚ) (-14:ℚ))
    apply hr.trans_lt
    simp only [degree_mul,degree_X_add_C]
    norm_num
private theorem moment_13_0 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    L ⟨.V,1,3,2⟩ z (X^0) = -4/z := by
  rw [moment_partial_fractions _ _ _ hz h1,quotient_13_0]
  have hd : (1:ℚ[X]).natDegree = 0 := by compute_degree <;> norm_num
  rw [hd]
  norm_num [poleSet,residue,weightNum,weightDen,omega,liNeg,
    Finset.sum_Ico_succ_top,Finset.prod_Ico_succ_top,
    Finset.sum_Icc_succ_top,Finset.sum_range_succ,Finset.prod_range_succ,
    Polynomial.coeff_X,Nat.stirlingSecond_one_right]
  field_simp [hz,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
private theorem moment_13_1 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    L ⟨.V,1,3,2⟩ z (X^1) = 1+8/z+z/(1-z) := by
  rw [moment_partial_fractions _ _ _ hz h1,quotient_13_1]
  have hd : (X-3:ℚ[X]).natDegree = 1 := by compute_degree <;> norm_num
  rw [hd]
  norm_num [poleSet,residue,weightNum,weightDen,omega,liNeg,
    Finset.sum_Ico_succ_top,Finset.prod_Ico_succ_top,
    Finset.sum_Icc_succ_top,Finset.sum_range_succ,Finset.prod_range_succ,
    Polynomial.coeff_X,Nat.stirlingSecond_one_right]
  field_simp [hz,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
private theorem moment_13_2 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    L ⟨.V,1,3,2⟩ z (X^2) = -3-16/z-3*z/(1-z)+2*z/(1-z)^2 := by
  rw [moment_partial_fractions _ _ _ hz h1,quotient_13_2]
  have hd : (X^2-3*X+7:ℚ[X]).natDegree = 2 := by compute_degree <;> norm_num
  rw [hd]
  norm_num [poleSet,residue,weightNum,weightDen,omega,liNeg,
    Finset.sum_Ico_succ_top,Finset.prod_Ico_succ_top,
    Finset.sum_Icc_succ_top,Finset.sum_range_succ,Finset.prod_range_succ,
    Polynomial.coeff_X,Nat.stirlingSecond_one_right]
  field_simp [hz,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
private theorem num_14 : weightNum ⟨.V,1,4,2⟩=(X^2:ℚ[X]) := by norm_num [weightNum]
private theorem den_14 : weightDen ⟨.V,1,4,2⟩=((X+C (1:ℚ))*(X+C (2:ℚ))*(X+C (3:ℚ)):ℚ[X]) := by
  norm_num [weightDen,poleSet,Finset.prod_Ico_succ_top,Finset.prod_range_succ,map_ofNat]
private theorem quotient_14_0 : polyPart ⟨.V,1,4,2⟩ (X^0)=(0:ℚ[X]) := by
  rw [polyPart,num_14,den_14]
  apply (div_modByMonic_unique (0) (C (1:ℚ)*X^2+C (0:ℚ)*X^1+C (0:ℚ)*X^0) ?_ ⟨by norm_num only [map_ofNat,map_neg,map_zero,map_one];ring,?_⟩).1
  · repeat' apply Monic.mul
    all_goals exact monic_X_add_C _
  · have hr : degree (C (1:ℚ)*X^2+C (0:ℚ)*X^1+C (0:ℚ)*X^0:ℚ[X]) ≤ 2 := by
      simpa only [pow_zero,mul_one,pow_one] using (degree_quadratic (1:ℚ) (0:ℚ) (0:ℚ))
    apply hr.trans_lt
    simp only [degree_mul,degree_X_add_C]
    norm_num
private theorem quotient_14_1 : polyPart ⟨.V,1,4,2⟩ (X^1)=(1:ℚ[X]) := by
  rw [polyPart,num_14,den_14]
  apply (div_modByMonic_unique (1) (C (-6:ℚ)*X^2+C (-11:ℚ)*X^1+C (-6:ℚ)*X^0) ?_ ⟨by norm_num only [map_ofNat,map_neg,map_zero,map_one];ring,?_⟩).1
  · repeat' apply Monic.mul
    all_goals exact monic_X_add_C _
  · have hr : degree (C (-6:ℚ)*X^2+C (-11:ℚ)*X^1+C (-6:ℚ)*X^0:ℚ[X]) ≤ 2 := by
      simpa only [pow_zero,mul_one,pow_one] using (degree_quadratic (-6:ℚ) (-11:ℚ) (-6:ℚ))
    apply hr.trans_lt
    simp only [degree_mul,degree_X_add_C]
    norm_num
private theorem quotient_14_2 : polyPart ⟨.V,1,4,2⟩ (X^2)=(X-6:ℚ[X]) := by
  rw [polyPart,num_14,den_14]
  apply (div_modByMonic_unique (X-6) (C (25:ℚ)*X^2+C (60:ℚ)*X^1+C (36:ℚ)*X^0) ?_ ⟨by norm_num only [map_ofNat,map_neg,map_zero,map_one];ring,?_⟩).1
  · repeat' apply Monic.mul
    all_goals exact monic_X_add_C _
  · have hr : degree (C (25:ℚ)*X^2+C (60:ℚ)*X^1+C (36:ℚ)*X^0:ℚ[X]) ≤ 2 := by
      simpa only [pow_zero,mul_one,pow_one] using (degree_quadratic (25:ℚ) (60:ℚ) (36:ℚ))
    apply hr.trans_lt
    simp only [degree_mul,degree_X_add_C]
    norm_num
private theorem moment_14_0 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    L ⟨.V,1,4,2⟩ z (X^0) = 9/(2*z^2)-23/(8*z) := by
  rw [moment_partial_fractions _ _ _ hz h1,quotient_14_0]
  have hd : (0:ℚ[X]).natDegree = 0 := by norm_num
  rw [hd]
  norm_num [poleSet,residue,weightNum,weightDen,omega,liNeg,
    Finset.sum_Ico_succ_top,Finset.prod_Ico_succ_top,
    Finset.sum_Icc_succ_top,Finset.sum_range_succ,Finset.prod_range_succ,
    Polynomial.coeff_X,Nat.stirlingSecond_one_right]
  field_simp [hz,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
private theorem moment_14_1 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    L ⟨.V,1,4,2⟩ z (X^1) = -27/(2*z^2)+37/(8*z) := by
  rw [moment_partial_fractions _ _ _ hz h1,quotient_14_1]
  have hd : (1:ℚ[X]).natDegree = 0 := by compute_degree <;> norm_num
  rw [hd]
  norm_num [poleSet,residue,weightNum,weightDen,omega,liNeg,
    Finset.sum_Ico_succ_top,Finset.prod_Ico_succ_top,
    Finset.sum_Icc_succ_top,Finset.sum_range_succ,Finset.prod_range_succ,
    Polynomial.coeff_X,Nat.stirlingSecond_one_right]
  field_simp [hz,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
private theorem moment_14_2 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    L ⟨.V,1,4,2⟩ z (X^2) = 81/(2*z^2)-47/(8*z)+1+z/(1-z) := by
  rw [moment_partial_fractions _ _ _ hz h1,quotient_14_2]
  have hd : (X-6:ℚ[X]).natDegree = 1 := by compute_degree <;> norm_num
  rw [hd]
  norm_num [poleSet,residue,weightNum,weightDen,omega,liNeg,
    Finset.sum_Ico_succ_top,Finset.prod_Ico_succ_top,
    Finset.sum_Icc_succ_top,Finset.sum_range_succ,Finset.prod_range_succ,
    Polynomial.coeff_X,Nat.stirlingSecond_one_right]
  field_simp [hz,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
private theorem num_03 : weightNum ⟨.V,0,3,3⟩=(1:ℚ[X]) := by norm_num [weightNum]
private theorem den_03 : weightDen ⟨.V,0,3,3⟩=((X+C (0:ℚ))*(X+C (1:ℚ))*(X+C (2:ℚ)):ℚ[X]) := by
  norm_num [weightDen,poleSet,Finset.prod_Ico_succ_top,Finset.prod_range_succ,map_ofNat]
private theorem quotient_03_0 : polyPart ⟨.V,0,3,3⟩ (X^0)=(0:ℚ[X]) := by
  rw [polyPart,num_03,den_03]
  apply (div_modByMonic_unique (0) (C (0:ℚ)*X^2+C (0:ℚ)*X^1+C (1:ℚ)*X^0) ?_ ⟨by norm_num only [map_ofNat,map_neg,map_zero,map_one];ring,?_⟩).1
  · repeat' apply Monic.mul
    all_goals exact monic_X_add_C _
  · have hr : degree (C (0:ℚ)*X^2+C (0:ℚ)*X^1+C (1:ℚ)*X^0:ℚ[X]) ≤ 2 := by
      simpa only [pow_zero,mul_one,pow_one] using (degree_quadratic (0:ℚ) (0:ℚ) (1:ℚ))
    apply hr.trans_lt
    simp only [degree_mul,degree_X_add_C]
    norm_num
private theorem quotient_03_1 : polyPart ⟨.V,0,3,3⟩ (X^1)=(0:ℚ[X]) := by
  rw [polyPart,num_03,den_03]
  apply (div_modByMonic_unique (0) (C (0:ℚ)*X^2+C (1:ℚ)*X^1+C (0:ℚ)*X^0) ?_ ⟨by norm_num only [map_ofNat,map_neg,map_zero,map_one];ring,?_⟩).1
  · repeat' apply Monic.mul
    all_goals exact monic_X_add_C _
  · have hr : degree (C (0:ℚ)*X^2+C (1:ℚ)*X^1+C (0:ℚ)*X^0:ℚ[X]) ≤ 2 := by
      simpa only [pow_zero,mul_one,pow_one] using (degree_quadratic (0:ℚ) (1:ℚ) (0:ℚ))
    apply hr.trans_lt
    simp only [degree_mul,degree_X_add_C]
    norm_num
private theorem quotient_03_2 : polyPart ⟨.V,0,3,3⟩ (X^2)=(0:ℚ[X]) := by
  rw [polyPart,num_03,den_03]
  apply (div_modByMonic_unique (0) (C (1:ℚ)*X^2+C (0:ℚ)*X^1+C (0:ℚ)*X^0) ?_ ⟨by norm_num only [map_ofNat,map_neg,map_zero,map_one];ring,?_⟩).1
  · repeat' apply Monic.mul
    all_goals exact monic_X_add_C _
  · have hr : degree (C (1:ℚ)*X^2+C (0:ℚ)*X^1+C (0:ℚ)*X^0:ℚ[X]) ≤ 2 := by
      simpa only [pow_zero,mul_one,pow_one] using (degree_quadratic (1:ℚ) (0:ℚ) (0:ℚ))
    apply hr.trans_lt
    simp only [degree_mul,degree_X_add_C]
    norm_num
private theorem quotient_03_3 : polyPart ⟨.V,0,3,3⟩ (X^3)=(1:ℚ[X]) := by
  rw [polyPart,num_03,den_03]
  apply (div_modByMonic_unique (1) (C (-3:ℚ)*X^2+C (-2:ℚ)*X^1+C (0:ℚ)*X^0) ?_ ⟨by norm_num only [map_ofNat,map_neg,map_zero,map_one];ring,?_⟩).1
  · repeat' apply Monic.mul
    all_goals exact monic_X_add_C _
  · have hr : degree (C (-3:ℚ)*X^2+C (-2:ℚ)*X^1+C (0:ℚ)*X^0:ℚ[X]) ≤ 2 := by
      simpa only [pow_zero,mul_one,pow_one] using (degree_quadratic (-3:ℚ) (-2:ℚ) (0:ℚ))
    apply hr.trans_lt
    simp only [degree_mul,degree_X_add_C]
    norm_num
private theorem quotient_03_4 : polyPart ⟨.V,0,3,3⟩ (X^4)=(X-3:ℚ[X]) := by
  rw [polyPart,num_03,den_03]
  apply (div_modByMonic_unique (X-3) (C (7:ℚ)*X^2+C (6:ℚ)*X^1+C (0:ℚ)*X^0) ?_ ⟨by norm_num only [map_ofNat,map_neg,map_zero,map_one];ring,?_⟩).1
  · repeat' apply Monic.mul
    all_goals exact monic_X_add_C _
  · have hr : degree (C (7:ℚ)*X^2+C (6:ℚ)*X^1+C (0:ℚ)*X^0:ℚ[X]) ≤ 2 := by
      simpa only [pow_zero,mul_one,pow_one] using (degree_quadratic (7:ℚ) (6:ℚ) (0:ℚ))
    apply hr.trans_lt
    simp only [degree_mul,degree_X_add_C]
    norm_num
private theorem moment_03_0 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    L ⟨.V,0,3,3⟩ z (X^0) = 1/(2*z)-7/8 := by
  rw [moment_partial_fractions _ _ _ hz h1,quotient_03_0]
  have hd : (0:ℚ[X]).natDegree = 0 := by norm_num
  rw [hd]
  norm_num [poleSet,residue,weightNum,weightDen,omega,liNeg,
    Finset.sum_Ico_succ_top,Finset.prod_Ico_succ_top,
    Finset.sum_Icc_succ_top,Finset.sum_range_succ,Finset.prod_range_succ,
    Polynomial.coeff_X,Nat.stirlingSecond_one_right]
  field_simp [hz,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
private theorem moment_03_1 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    L ⟨.V,0,3,3⟩ z (X^1) = 3/4-1/z := by
  rw [moment_partial_fractions _ _ _ hz h1,quotient_03_1]
  have hd : (0:ℚ[X]).natDegree = 0 := by norm_num
  rw [hd]
  norm_num [poleSet,residue,weightNum,weightDen,omega,liNeg,
    Finset.sum_Ico_succ_top,Finset.prod_Ico_succ_top,
    Finset.sum_Icc_succ_top,Finset.sum_range_succ,Finset.prod_range_succ,
    Polynomial.coeff_X,Nat.stirlingSecond_one_right]
  field_simp [hz,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
private theorem moment_03_2 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    L ⟨.V,0,3,3⟩ z (X^2) = 2/z-1/2 := by
  rw [moment_partial_fractions _ _ _ hz h1,quotient_03_2]
  have hd : (0:ℚ[X]).natDegree = 0 := by norm_num
  rw [hd]
  norm_num [poleSet,residue,weightNum,weightDen,omega,liNeg,
    Finset.sum_Ico_succ_top,Finset.prod_Ico_succ_top,
    Finset.sum_Icc_succ_top,Finset.sum_range_succ,Finset.prod_range_succ,
    Polynomial.coeff_X,Nat.stirlingSecond_one_right]
  field_simp [hz,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
private theorem moment_03_3 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    L ⟨.V,0,3,3⟩ z (X^3) = -4/z := by
  rw [moment_partial_fractions _ _ _ hz h1,quotient_03_3]
  have hd : (1:ℚ[X]).natDegree = 0 := by compute_degree <;> norm_num
  rw [hd]
  norm_num [poleSet,residue,weightNum,weightDen,omega,liNeg,
    Finset.sum_Ico_succ_top,Finset.prod_Ico_succ_top,
    Finset.sum_Icc_succ_top,Finset.sum_range_succ,Finset.prod_range_succ,
    Polynomial.coeff_X,Nat.stirlingSecond_one_right]
  field_simp [hz,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
private theorem moment_03_4 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    L ⟨.V,0,3,3⟩ z (X^4) = 1+8/z+z/(1-z) := by
  rw [moment_partial_fractions _ _ _ hz h1,quotient_03_4]
  have hd : (X-3:ℚ[X]).natDegree = 1 := by compute_degree <;> norm_num
  rw [hd]
  norm_num [poleSet,residue,weightNum,weightDen,omega,liNeg,
    Finset.sum_Ico_succ_top,Finset.prod_Ico_succ_top,
    Finset.sum_Icc_succ_top,Finset.sum_range_succ,Finset.prod_range_succ,
    Polynomial.coeff_X,Nat.stirlingSecond_one_right]
  field_simp [hz,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
theorem special_V132 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    KV 1 3 2 z = -(5*z+4)/(z*(1-z)^2) := by
  simp only [KV,K,Matrix.det_fin_two]
  norm_num
  have hm0 := moment_13_0 z hz h1
  norm_num only [pow_zero,pow_one] at hm0
  rw [hm0]
  have hm1 := moment_13_1 z hz h1
  norm_num only [pow_zero,pow_one] at hm1
  rw [hm1]
  have hm2 := moment_13_2 z hz h1
  norm_num only [pow_zero,pow_one] at hm2
  rw [hm2]
  field_simp [hz,sub_ne_zero.mpr h1,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
#print axioms special_V132
theorem special_V142 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    KV 1 4 2 z = -(z+12)*(13*z-12)/(8*z^3*(z-1)) := by
  simp only [KV,K,Matrix.det_fin_two]
  norm_num
  have hm0 := moment_14_0 z hz h1
  norm_num only [pow_zero,pow_one] at hm0
  rw [hm0]
  have hm1 := moment_14_1 z hz h1
  norm_num only [pow_zero,pow_one] at hm1
  rw [hm1]
  have hm2 := moment_14_2 z hz h1
  norm_num only [pow_zero,pow_one] at hm2
  rw [hm2]
  field_simp [hz,sub_ne_zero.mpr h1,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
#print axioms special_V142
theorem special_V033 (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    KV 0 3 3 z = (z+4)/(8*(z-1)) := by
  simp only [KV,K,Matrix.det_fin_three]
  norm_num
  have hm0 := moment_03_0 z hz h1
  norm_num only [pow_zero,pow_one] at hm0
  rw [hm0]
  have hm1 := moment_03_1 z hz h1
  norm_num only [pow_zero,pow_one] at hm1
  rw [hm1]
  have hm2 := moment_03_2 z hz h1
  norm_num only [pow_zero,pow_one] at hm2
  rw [hm2]
  have hm3 := moment_03_3 z hz h1
  norm_num only [pow_zero,pow_one] at hm3
  rw [hm3]
  have hm4 := moment_03_4 z hz h1
  norm_num only [pow_zero,pow_one] at hm4
  rw [hm4]
  field_simp [hz,sub_ne_zero.mpr h1,sub_ne_zero.mpr (Ne.symm h1)] <;> ring
#print axioms special_V033

theorem special_V131 (z : ℚ) (hz : z≠0) (h1 : z≠1) : KV 1 3 1 z = -4/z := by
  simp only [KV,K,Matrix.det_fin_one]
  norm_num only [Fin.val_zero,zero_add,pow_zero]
  have hm := moment_13_0 z hz h1
  norm_num only [pow_zero] at hm
  exact hm
#print axioms special_V131
end
end CatalanCore.Li2.NVMod
