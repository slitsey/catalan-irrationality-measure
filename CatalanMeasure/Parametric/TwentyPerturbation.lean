module
public import CatalanMeasure.Parametric.TwentyPerturbationSetup
public import CatalanMeasure.Parametric.TwentyPrefactor
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Filter Polynomial Finset
open scoped BigOperators Topology
noncomputable section

theorem twenty_base_bound_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,|aeval catalan (deltaPoly twenty N)| ≤
      Real.exp ((20*(N:ℝ))^2*(-twentyDualTarget+Real.log 2/2+ε)) :=by
  filter_upwards [twenty_weighted_atomMatrix_det_eventually (show 0<ε/2 by positivity),
    twenty_sheet_prefactor_eventually (show 0<ε/2 by positivity),eventually_gt_atTop (0:ℕ)]
    with N hd hp hN
  have hh :=hd (fun _ =>none)
  simp only [Option.elim,prod_const_one,mul_one,one_mul,CatalanMeasure.atomMatrix]
    at hh
  rw [aeval_catalan_deltaPoly twenty_admissible hN]
  have hb : |(twentyRealBaseMatrix N).det| ≤ twentyAtomBaseBound N (ε/2) :=by
    have he : (Matrix.of fun r k =>twentyRealBaseMatrix N r k)=twentyRealBaseMatrix N :=rfl
    rw [he] at hh
    exact hh
  refine hb.trans ?_
  unfold twentyAtomBaseBound
  calc
    _ ≤ Real.exp (ε/2*(20*(N:ℝ))^2)*
        Real.exp ((20*(N:ℝ))^2*(-twentyDualTarget+Real.log 2/2+ε/2)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ :=by rw [← Real.exp_add];congr 1;ring

theorem twenty_perturbation :
    ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,∀ x : ℝ,
      |x-catalan| ≤ Real.exp (-(120*(N:ℝ))) →
      |aeval x (deltaPoly twenty N)-aeval catalan (deltaPoly twenty N)| ≤
        Real.exp ((20*(N:ℝ))^2*(-twentyDualTarget+Real.log 2/2+ε)) :=by
  intro ε hε
  have h2 :=positive_polynomial_factor_eventually (2:ℝ) (by norm_num) 0
    (ε :=ε/3) (by positivity)
  filter_upwards [twenty_weighted_atomMatrix_det_eventually (show 0<ε/3 by positivity),
    twenty_sheet_prefactor_eventually (show 0<ε/3 by positivity),
    twenty_rho_condition_eventually,h2,eventually_gt_atTop (0:ℕ)]
    with N hd hp hr h2N hN
  intro x hx
  let δ :=x-catalan
  let M :=twentyAtomBaseBound N (ε/3)
  let c :=twentyAtomColumnCost N
  have hM : 0 ≤ M :=by
    unfold M twentyAtomBaseBound twentySheetPrefactor
    positivity
  have hc : 0 ≤ c :=by unfold c twentyAtomColumnCost;positivity
  have hmain :=CatalanMeasure.abs_det_add_atoms_sub_le_joint
    (twentyRealBaseMatrix N) (twentyAtomVectors N) (twentyAtomWeights N) δ hM hc hd
  rw [twenty_delta_matrix_eq hN x,aeval_catalan_deltaPoly twenty_admissible hN]
  change |_-(twentyRealBaseMatrix N).det| ≤ _
  refine hmain.trans ?_
  have hsmall : (twenty.n N:ℝ)*((18*N:ℕ)*(|δ| * c)) ≤ 1 :=by
    have he : |δ| * Real.exp (120*(N:ℝ)) ≤ 1 :=by
      calc
        _ ≤ Real.exp (-(120*(N:ℝ)))*Real.exp (120*(N:ℝ)) :=
          mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
        _ = _ :=by rw [← Real.exp_add];simp
    calc
      _ = |δ| * ((twenty.n N:ℝ)*(18*N:ℕ)*twentyAtomColumnCost N) :=by unfold c;ring
      _ ≤ |δ| * Real.exp (120*(N:ℝ)) :=mul_le_mul_of_nonneg_left hr (abs_nonneg _)
      _ ≤ _ :=he
  have hpw :=CatalanMeasure.one_add_pow_le_exp (t :=(18*N:ℕ)*(|δ| * c))
    (by positivity) (twenty.n N)
  have he1 : Real.exp 1<3 :=by have hh :=Real.exp_one_lt_d9;norm_num at hh ⊢;linarith only [hh]
  have hfactor : (1+(18*N:ℕ)*(|δ| * c))^(twenty.n N)-1 ≤ 2 :=by
    have he :=Real.exp_le_exp.mpr hsmall
    linarith only [hpw,he,he1]
  have hN1 : (1:ℝ) ≤ N :=by exact_mod_cast hN
  have htwo : (2:ℝ) ≤ Real.exp (ε/3*(20*(N:ℝ))^2) :=by
    simp only [pow_zero,mul_one] at h2N
    have hs : (N:ℝ) ≤ (20*(N:ℝ))^2 :=by nlinarith only [hN1]
    exact h2N.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ ε/3)))
  calc
    _ ≤ M*2 :=mul_le_mul_of_nonneg_left hfactor hM
    _ ≤ M*Real.exp (ε/3*(20*(N:ℝ))^2) :=mul_le_mul_of_nonneg_left htwo hM
    _ ≤ (Real.exp (ε/3*(20*(N:ℝ))^2)*
        Real.exp ((20*(N:ℝ))^2*(-twentyDualTarget+Real.log 2/2+ε/3)))*
          Real.exp (ε/3*(20*(N:ℝ))^2) :=by
      unfold M twentyAtomBaseBound
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ :=by rw [← Real.exp_add,← Real.exp_add];congr 1;ring

end
end CatalanMeasure.Parametric
