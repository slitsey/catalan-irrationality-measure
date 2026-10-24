module
public import CatalanArchive.CatalanMeasure.Parametric.GapQuadrature
public import CatalanArchive.CatalanMeasure.Parametric.GapCircleCover
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset OAI.InternalCatalan
noncomputable section

def GapCircleBound : Prop := ∀ (N : ℕ) (z : ℂ), ‖z‖=(1001/1000:ℝ) →
    ‖((gapPolynomial (interpolationGap:ℝ) N).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1:ℂ)-z‖^(2*N) ≤ Real.exp (gapWeightCost*N)

theorem gap_common_basis_coeff_zero (N : ℕ) (a : Fin (18*N)) (i : ℕ)
    (hi : twenty.H N ≤ i) :
    (rowCommonFactor twenty N*quadBasis (twentyGapNodes N) a).coeff i=0 := by
  have hf := rowCommonFactor_natDegree_le twenty N
  have hb := quadBasis_natDegree_le (twenty_gap_nodes_properties N).1 a
  have hd : (rowCommonFactor twenty N*quadBasis (twentyGapNodes N) a).natDegree ≤
      (rowCommonFactor twenty N).natDegree+(quadBasis (twentyGapNodes N) a).natDegree :=
    natDegree_mul_le
  apply coeff_eq_zero_of_natDegree_lt
  rw [twenty_A] at hf
  change (rowCommonFactor twenty N).natDegree ≤ 8*N+1*N at hf
  rw [twenty_H] at hi
  have hN : 0<N := by have := a.isLt; omega
  omega

theorem gap_filtered_basis_le (hcircle : GapCircleBound) (N : ℕ) (a : Fin (18*N)) (z : ℂ)
    (hz : ‖z‖=(TwentyCircle.twentyRadius:ℝ)) :
    ‖((quadBasis (twentyGapNodes N) a*(1-X)^(2*N)).map
      (algebraMap ℝ ℂ)).eval z‖ ≤ 1000*Real.exp (gapWeightCost*N) := by
  have hN : 0<N := by have := a.isLt; omega
  have ha0 : (0:ℝ) < interpolationGap := by norm_num [interpolationGap]
  have ha1 : (interpolationGap:ℝ)<1 := by norm_num [interpolationGap]
  let d : ℝ := 36*N*(interpolationGap:ℝ)/(1-(interpolationGap:ℝ)^2)
  have hd : 1 ≤ d := by
    have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
    dsimp [d]
    norm_num [interpolationGap]
    nlinarith only [hNR]
  have hcard := norm_cardinal_le_of_nodal (gap_nodes_injective ha0 ha1 N)
    (fun i => (gap_nodes_bounds ha0 ha1 N i).1) a
    (gap_polynomial_eq_nodal ha0 ha1 hN)
    (lt_of_lt_of_le (by norm_num) hd)
    (gap_polynomial_derivative_ge ha0 ha1 N a)
    (by norm_num [TwentyCircle.twentyRadius]) z hz
  have hb : ‖((quadBasis (twentyGapNodes N) a).map (algebraMap ℝ ℂ)).eval z‖ ≤
      1000*‖((gapPolynomial (interpolationGap:ℝ) N).map (algebraMap ℝ ℂ)).eval z‖ := by
    apply hcard.trans
    apply (div_le_iff₀ (mul_pos (lt_of_lt_of_le (by norm_num) hd)
      (by norm_num [TwentyCircle.twentyRadius]))).mpr
    have he : 1000*((TwentyCircle.twentyRadius:ℝ)-1)=1 := by norm_num [TwentyCircle.twentyRadius]
    calc
      _  ≤  ‖((gapPolynomial (interpolationGap:ℝ) N).map (algebraMap ℝ ℂ)).eval z‖*d :=
        le_mul_of_one_le_right (norm_nonneg _) hd
      _ = _ := by norm_num [TwentyCircle.twentyRadius] <;> ring
  rw [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_one,
    Polynomial.map_X,eval_mul,eval_pow,eval_sub,eval_one,eval_X,norm_mul,norm_pow]
  calc
    _  ≤  (1000*‖((gapPolynomial (interpolationGap:ℝ) N).map (algebraMap ℝ ℂ)).eval z‖)*
        ‖(1:ℂ)-z‖^(2*N) := mul_le_mul_of_nonneg_right hb (by positivity)
    _  ≤  _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hcircle N z (by simpa [TwentyCircle.twentyRadius] using hz)

theorem gap_functional_le (hcircle : GapCircleBound) (N k : ℕ) (a : Fin (18*N)) :
    |polynomialFunctional twenty N k (rowCommonFactor twenty N*
      quadBasis (twentyGapNodes N) a)| ≤ 108000*N*Real.exp (gapWeightCost*N) := by
  have hh := polynomialFunctional_common_factor_le twenty N k
    (quadBasis (twentyGapNodes N) a) (gap_common_basis_coeff_zero N a)
    (radius := (TwentyCircle.twentyRadius:ℝ)) (B := 1000*Real.exp (gapWeightCost*N))
    (by norm_num [TwentyCircle.twentyRadius]) (fun z hz => by
      simpa only [Parameters.h,Parameters.q,twenty,
        show 1*N+1*N=2*N by ring] using gap_filtered_basis_le hcircle N a z hz)
  rw [twenty_H] at hh
  convert hh using 1 <;> push_cast <;> ring

theorem gap_weight_joint_le (hcircle : GapCircleBound) (N k : ℕ) (a : Fin (18*N)) :
    |(rowCommonFactor twenty N).eval (twentyGapNodes N a)| *
      |restrictedWeight twenty N k (twentyGapNodes N) a| ≤
        108000*N*Real.exp (gapWeightCost*N) := by
  have hi := gap_nodes_bounds
    (show (0:ℝ) < interpolationGap by norm_num [interpolationGap])
    (show (interpolationGap:ℝ)<1 by norm_num [interpolationGap]) N a
  have hzero : twentyGapNodes N a≠0 := by
    intro h
    have hh := hi.2
    change (interpolationGap:ℝ)< |twentyGapNodes N a| at hh
    rw [h,abs_zero] at hh
    norm_num [interpolationGap] at hh
  have hn := rowCommonFactor_eval_ne_zero_of twenty N hzero hi.1.2.ne
  rw [restrictedWeight,abs_div,mul_comm,div_mul_cancel₀ _ (abs_ne_zero.mpr hn)]
  exact gap_functional_le hcircle N k a

end
end CatalanMeasure.Parametric
