module
public import CatalanMeasure.Parametric.TwentyAtomDeterminants
public import CatalanMeasure.JointDetExpansion
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Polynomial Matrix Finset Filter
open scoped BigOperators Topology
noncomputable section

theorem twenty_delta_matrix_eq {N : ℕ} (hN : 0<N) (x : ℝ) :
    aeval x (deltaPoly twenty N)=
      (Matrix.of fun r k : Fin (twenty.n N) =>twentyRealBaseMatrix N r k+
        (x-catalan)*∑ a,twentyAtomVectors N r a*twentyAtomWeights N a k).det :=by
  have hh :=AlgHom.map_det (aeval (R :=ℚ) x)
    ((X:ℚ[X]) • (measureCatalanMatrix twenty N).map C+(measureBaseMatrix twenty N).map C)
  unfold deltaPoly
  rw [hh]
  congr 1
  ext r k
  rw [AlgHom.mapMatrix_apply,Matrix.map_apply,deltaPoly_matrix_entry]
  simp only [map_add,map_mul,aeval_X,aeval_C,eq_ratCast,Matrix.of_apply,
    twentyRealBaseMatrix,twentyAtomVectors,twentyAtomWeights]
  have hw :=filteredCatalanCoeff_restricted_weights twenty_admissible hN r.isLt
    (show twenty.n N-twenty.g N ≤ 18*N by change 20*N-2*N ≤ 18*N;omega)
    (CatalanMeasure.chebNode_injective (18*N)) (fun a =>(CatalanMeasure.chebNode_mem a).2) k.val
  have he : (∑ a : Fin (18*N),realRowAmplitude twenty N r.val (CatalanMeasure.chebNode (18*N) a)*
      restrictedWeight twenty N k.val (CatalanMeasure.chebNode (18*N)) a)=
      (filteredCatalanCoeffRat twenty N r.val k.val:ℝ) :=by
    rw [hw]
    apply sum_congr rfl
    intro a _
    rw [realRowAmplitude_of_nonpos twenty N r.val (CatalanMeasure.chebNode_mem a).2.le]
  rw [he,← filteredEntry_real_affine twenty_admissible hN r.isLt k.isLt]
  ring

theorem positive_polynomial_factor_eventually (C : ℝ) (hC : 0<C) (d : ℕ)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,C*(N:ℝ)^d ≤ Real.exp (ε*(N:ℝ)) :=by
  have hi : Tendsto (fun N : ℕ =>(N:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ =>Real.log (N:ℝ)/(N:ℝ)) atTop (𝓝 0) :=by
    simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ =>(N:ℝ)) atTop atTop)
  have ht :=(hi.const_mul (Real.log C)).add (hl.const_mul (d:ℝ))
  simp only [mul_zero,add_zero] at ht
  have he :=(tendsto_order.mp ht).2 ε hε
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with N heN hN
  have hn : (0:ℝ)<N :=by exact_mod_cast hN
  have hlog : Real.log C+(d:ℝ)*Real.log (N:ℝ)<ε*(N:ℝ) :=by
    have hh :=(div_lt_iff₀ hn).mp
      (show (Real.log C+(d:ℝ)*Real.log (N:ℝ))/(N:ℝ)<ε by
        simpa only [add_div,div_eq_mul_inv,add_mul,mul_assoc] using heN)
    exact hh
  have hx : C*(N:ℝ)^d=Real.exp (Real.log C+(d:ℝ)*Real.log (N:ℝ)) :=by
    rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log hC,Real.exp_log hn]
  rw [hx]
  exact Real.exp_le_exp.mpr hlog.le

theorem twenty_rho_condition_eventually :
    ∀ᶠ N : ℕ in atTop,(twenty.n N:ℝ)*(18*N:ℕ)*twentyAtomColumnCost N ≤
      Real.exp (120*(N:ℝ)) :=by
  have hh :=positive_polynomial_factor_eventually (19440000:ℝ) (by norm_num) 3
    (ε :=1) (by norm_num)
  filter_upwards [hh] with N hN
  have hn : twenty.n N=20*N :=rfl
  unfold twentyAtomColumnCost
  rw [hn]
  push_cast
  calc
    _ = (19440000*(N:ℝ)^3)*Real.exp (119*(N:ℝ)) :=by ring
    _ ≤ Real.exp (1*(N:ℝ))*Real.exp (119*(N:ℝ)) :=
      mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
    _ = _ :=by rw [← Real.exp_add];congr 1;ring

end
end CatalanMeasure.Parametric
