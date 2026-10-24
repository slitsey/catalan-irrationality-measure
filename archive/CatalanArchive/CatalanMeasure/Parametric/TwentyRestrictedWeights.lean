module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyParameters
public import CatalanArchive.CatalanMeasure.Parametric.TwentyRadiusQuadrature
public import CatalanMeasure.Parametric.RestrictedWeights
public import CatalanMeasure.Parametric.CommonFactorCoordinate
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset OAI.InternalCatalan
noncomputable section
theorem twenty_common_basis_coeff_zero (N : ℕ) (a : Fin (18*N)) (i : ℕ)
    (hi : twenty.H N ≤ i) :
    (rowCommonFactor twenty N *
      OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (18*N)) a).coeff i=0 := by
  have hf := rowCommonFactor_natDegree_le twenty N
  have hb := quadBasis_natDegree_le (CatalanMeasure.chebNode_injective (18*N)) a
  have hd : (rowCommonFactor twenty N *
      OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (18*N)) a).natDegree ≤
      (rowCommonFactor twenty N).natDegree +
      (OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (18*N)) a).natDegree := natDegree_mul_le
  apply coeff_eq_zero_of_natDegree_lt
  rw [twenty_A] at hf
  change (rowCommonFactor twenty N).natDegree ≤ 8*N+1*N at hf
  rw [twenty_H] at hi
  have hN : 0<N := by have := a.isLt; omega
  omega

theorem twenty_restricted_functional_le (N k : ℕ) (a : Fin (18*N)) :
    |polynomialFunctional twenty N k (rowCommonFactor twenty N *
      OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (18*N)) a)| ≤
      54000*N*(TwentyCircle.twentyCircleK:ℝ)^N := by
  have hh := polynomialFunctional_common_factor_le twenty N k
    (OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (18*N)) a)
    (twenty_common_basis_coeff_zero N a)
    (radius := (TwentyCircle.twentyRadius:ℝ)) (B := 500*(TwentyCircle.twentyCircleK:ℝ)^N)
    (by norm_num [TwentyCircle.twentyRadius]) (fun z hz => by
      simpa only [Parameters.h,Parameters.q,twenty,show 1*N+1*N=2*N by ring] using
        twenty_norm_restricted_filtered_basis_le N a z hz)
  rw [twenty_H] at hh
  convert hh using 1 <;> push_cast <;> ring

theorem twenty_restrictedWeight_joint_le (N k : ℕ) (a : Fin (18*N)) :
    |(rowCommonFactor twenty N).eval (CatalanMeasure.chebNode (18*N) a)| *
      |restrictedWeight twenty N k (CatalanMeasure.chebNode (18*N)) a| ≤
      54000*N*(TwentyCircle.twentyCircleK:ℝ)^N := by
  have hn := rowCommonFactor_eval_ne_zero twenty N (CatalanMeasure.chebNode_mem a).2
  rw [restrictedWeight,abs_div,mul_comm,div_mul_cancel₀ _ (abs_ne_zero.mpr hn)]
  exact twenty_restricted_functional_le N k a


theorem twenty_commonFactor_pow (N : ℕ) :
    rowCommonFactor twenty N=(rowCommonFactor twenty 1)^N := by
  unfold rowCommonFactor
  rw [twenty_A N,twenty_A 1]
  change (X^(8*N)*(1-X)^(1*N):ℝ[X])=(X^8*(1-X)^1)^N
  rw [mul_pow,pow_mul,pow_mul]

theorem twenty_commonFactor_log_scale (N : ℕ) (t : ℝ) :
    Real.log |(rowCommonFactor twenty N).eval t| =
      (N:ℝ)*Real.log |(rowCommonFactor twenty 1).eval t| := by
  rw [twenty_commonFactor_pow,eval_pow,abs_pow,Real.log_pow]

theorem twenty_weighted_restrictedWeight_le (N k : ℕ) (a : Fin (18*N)) {x W S : ℝ}
    (hx : x<0) (hcoord : realCoordinateInv x=CatalanMeasure.chebNode (18*N) a)
    (hfield : 20*W-Real.log |(rowCommonFactor twenty 1).eval (realCoordinateInv x)|≤S) :
    Real.exp (20*N*W)*|restrictedWeight twenty N k (CatalanMeasure.chebNode (18*N)) a| ≤
      54000*N*Real.exp ((33+S)*N) := by
  set c := |(rowCommonFactor twenty N).eval (CatalanMeasure.chebNode (18*N) a)| with hc
  have hcpos : 0<c := abs_pos.mpr (rowCommonFactor_eval_ne_zero twenty N
    (CatalanMeasure.chebNode_mem a).2)
  have hlog : Real.log c=(N:ℝ)*Real.log |(rowCommonFactor twenty 1).eval (realCoordinateInv x)| := by
    rw [hc,twenty_commonFactor_log_scale,← hcoord]
  have hr : Real.exp (20*N*W)/c =
      Real.exp ((20*W-Real.log |(rowCommonFactor twenty 1).eval (realCoordinateInv x)|)*N) := by
    rw [← Real.exp_log hcpos,← Real.exp_sub,hlog]
    congr 1
    ring
  have hratio : Real.exp (20*N*W)/c≤Real.exp (S*N) := by
    rw [hr]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hfield (Nat.cast_nonneg N)
  have hweight := twenty_restrictedWeight_joint_le N k a
  change c*|restrictedWeight twenty N k (CatalanMeasure.chebNode (18*N)) a|≤
    54000*N*(TwentyCircle.twentyCircleK:ℝ)^N at hweight
  have hK0 : (0:ℝ)≤TwentyCircle.twentyCircleK := by norm_num [TwentyCircle.twentyCircleK]
  have hK : (TwentyCircle.twentyCircleK:ℝ)^N≤Real.exp (33*N) := by
    calc _ ≤ Real.exp 33 ^N := pow_le_pow_left₀ hK0 TwentyCircle.twentyCircleK_le_exp N
      _ = Real.exp (33*N) := by rw [← Real.exp_nat_mul];congr 1;ring
  calc
    _ = (Real.exp (20*N*W)/c)*
        (c*|restrictedWeight twenty N k (CatalanMeasure.chebNode (18*N)) a|) := by
          field_simp
    _ ≤ Real.exp (S*N)*(54000*N*(TwentyCircle.twentyCircleK:ℝ)^N) :=
      mul_le_mul hratio hweight (by positivity) (Real.exp_pos _).le
    _ ≤ Real.exp (S*N)*(54000*N*Real.exp (33*N)) := by gcongr
    _ = 54000*N*Real.exp ((33+S)*N) := by
      have he : Real.exp (S*N)*Real.exp (33*N)=Real.exp ((33+S)*N) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (54000*(N:ℝ))*(Real.exp (S*N)*Real.exp (33*N)) := by ring
        _ = _ := by rw [he]


end
end CatalanMeasure.Parametric
