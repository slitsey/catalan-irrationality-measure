module
public import CatalanArchive.CatalanMeasure.Parametric.TargetAtomCost
public import CatalanArchive.CatalanMeasure.Parametric.TwentyCostMain
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Polynomial Filter Real Finset
open scoped Nat Topology BigOperators
noncomputable section

def measureGapAt (target : ℝ) : ℝ := target-Real.log 2/2-
  (8795/4800+(21/200)*Real.log 2)

theorem base_bound_at_target (target ρ : ℝ) (hpoint : WeightedAtomPointAt target ρ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,|aeval catalan (deltaPoly twenty N)| ≤
      Real.exp ((20*(N:ℝ))^2*(-target+Real.log 2/2+ε)) :=by
  filter_upwards [weighted_atom_det_at_target target ρ hpoint (show 0<ε/2 by positivity),
    twenty_sheet_prefactor_eventually (show 0<ε/2 by positivity),eventually_gt_atTop (0:ℕ)]
    with N hd hp hN
  have hh :=hd (fun _ =>none)
  simp only [Option.elim,prod_const_one,mul_one,one_mul,CatalanMeasure.atomMatrix]
    at hh
  rw [aeval_catalan_deltaPoly twenty_admissible hN]
  have hb : |(twentyRealBaseMatrix N).det| ≤ atomBaseBoundAt target N (ε/2) :=by
    have he : (Matrix.of fun r k =>twentyRealBaseMatrix N r k)=twentyRealBaseMatrix N :=rfl
    rw [he] at hh
    exact hh
  refine hb.trans ?_
  unfold atomBaseBoundAt
  calc
    _ ≤ Real.exp (ε/2*(20*(N:ℝ))^2)*
        Real.exp ((20*(N:ℝ))^2*(-target+Real.log 2/2+ε/2)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ :=by rw [← Real.exp_add];congr 1;ring

theorem perturbation_at_target (target ρ : ℝ)
    (hpoint : WeightedAtomPointAt target ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x-catalan| ≤ Real.exp (-(ρ*(N : ℝ))) →
      |aeval x (deltaPoly twenty N)-aeval catalan (deltaPoly twenty N)| ≤
        Real.exp ((20*(N : ℝ))^2*(-target+Real.log 2/2+ε)) := by
  filter_upwards [weighted_atom_det_at_target target ρ hpoint
      (show 0 < ε/3 by positivity),
    twenty_sheet_prefactor_eventually (show 0 < ε/3 by positivity),
    twenty_joint_factor_of_cost_eventually ρ (show 0 < ε/3 by positivity),
    eventually_gt_atTop (0 : ℕ)] with N hd hp hf hN x hx
  let δ : ℝ := x-catalan
  let M : ℝ := atomBaseBoundAt target N (ε/3)
  let c : ℝ := twentyParametricAtomColumnCost ρ N
  have hM : 0 ≤ M := by unfold M atomBaseBoundAt twentySheetPrefactor; positivity
  have hc : 0 ≤ c := by unfold c twentyParametricAtomColumnCost; positivity
  have hmain := CatalanMeasure.abs_det_add_atoms_sub_le_joint
    (twentyRealBaseMatrix N) (twentyFullAtomVectors N) (twentyFullAtomWeights N)
    δ hM hc hd
  rw [twenty_full_delta_matrix_eq hN x, aeval_catalan_deltaPoly twenty_admissible hN]
  change |_-(twentyRealBaseMatrix N).det| ≤ _
  have hfactor : (1+(18*N : ℕ)*(|δ| * c))^(twenty.n N)-1 ≤
      Real.exp (ε/3*(20*(N : ℝ))^2) := by
    have hh := hf δ hx
    dsimp [c]
    linarith only [hh]
  calc
    _ ≤ M*Real.exp (ε/3*(20*(N : ℝ))^2) :=
      hmain.trans (mul_le_mul_of_nonneg_left hfactor hM)
    _ ≤ (Real.exp (ε/3*(20*(N : ℝ))^2)*
        Real.exp ((20*(N : ℝ))^2*(-target+Real.log 2/2+ε/3)))*
          Real.exp (ε/3*(20*(N : ℝ))^2) := by
      unfold M atomBaseBoundAt
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring


theorem integer_poly_hypotheses_at_target (target ρ : ℝ)
    (hpoint : WeightedAtomPointAt target ρ) {η : ℝ} (hη : η<400*measureGapAt target) :
    ∃ P₀ : ℕ,
      (∀ p,P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ),0<b → ¬p^2∣b →
        aeval ((a:ℝ)/b) (twentyMeasureIntPoly p)≠0) ∧
      (∀ p,P₀ ≤ p → p.Prime → ∀ x : ℝ,|x-catalan| ≤ Real.exp (-(ρ*(p:ℝ))) →
        |aeval x (twentyMeasureIntPoly p)| ≤ Real.exp (-(η*(p:ℝ)^2))) :=by
  let e : ℝ :=(400*measureGapAt target-η)/1600
  have he : 0<e :=by unfold e;linarith only [hη]
  have h2 :=positive_polynomial_factor_eventually (2:ℝ) (by norm_num) 0 (ε :=e) he
  have hev : ∀ᶠ p : ℕ in atTop,finitePrimeCutoff twenty<p ∧ 1000000000000 ≤ p ∧
      (∀ x : ℝ,|x-catalan| ≤ Real.exp (-(ρ*(p:ℝ))) →
        |aeval x (twentyMeasureIntPoly p)| ≤ Real.exp (-(η*(p:ℝ)^2))) :=by
    filter_upwards [perturbation_at_target target ρ hpoint he,base_bound_at_target target ρ hpoint he,
      twenty_log_denomBound_eventually_le he,twenty_factorial_eventually he,h2,
      eventually_gt_atTop (finitePrimeCutoff twenty),eventually_ge_atTop (1000000000000:ℕ)]
      with p hpert hbase hden hfac htwo hcut hbig
    refine ⟨hcut,hbig,?_⟩
    intro x hx
    have hp : 0<p :=by omega
    have hp1 : (1:ℝ) ≤ p :=by exact_mod_cast hp
    let E : ℝ :=(20*(p:ℝ))^2*(-target+Real.log 2/2+e)
    have hΔ : |aeval x (deltaPoly twenty p)| ≤ 2*Real.exp E :=by
      calc
        _ = |(aeval x (deltaPoly twenty p)-aeval catalan (deltaPoly twenty p))+
          aeval catalan (deltaPoly twenty p)| :=by rw [sub_add_cancel]
        _ ≤ |aeval x (deltaPoly twenty p)-aeval catalan (deltaPoly twenty p)|+
          |aeval catalan (deltaPoly twenty p)| :=abs_add_le _ _
        _ ≤ Real.exp E+Real.exp E :=add_le_add (hpert x hx) hbase
        _ = _ :=by ring
    have hD : (twentyDenomBound p:ℝ) ≤
        Real.exp ((8795/4800+(21/200)*Real.log 2+e)*(20*(p:ℝ))^2) :=by
      rw [← Real.exp_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (twentyDenomBound_ne_zero p)))]
      exact Real.exp_le_exp.mpr hden
    have htwo' : (2:ℝ) ≤ Real.exp (e*(20*(p:ℝ))^2) :=by
      simp only [pow_zero,mul_one] at htwo
      have hs : (p:ℝ) ≤ (20*(p:ℝ))^2 :=by nlinarith only [hp1]
      exact htwo.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs he.le))
    rw [aeval_twentyMeasureIntPoly hbig,abs_mul,abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((18*p)!:ℝ)),
      abs_of_nonneg (Nat.cast_nonneg (twentyDenomBound p))]
    calc
      _ ≤ Real.exp (e*(20*(p:ℝ))^2)*
          Real.exp ((8795/4800+(21/200)*Real.log 2+e)*(20*(p:ℝ))^2)*
          (2*Real.exp E) :=by gcongr
      _ ≤ Real.exp (e*(20*(p:ℝ))^2)*
          Real.exp ((8795/4800+(21/200)*Real.log 2+e)*(20*(p:ℝ))^2)*
          (Real.exp (e*(20*(p:ℝ))^2)*Real.exp E) :=by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right htwo' (Real.exp_pos _).le) (by positivity)
      _ = _ :=by
        rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
        congr 1
        unfold E e measureGapAt
        ring
  obtain ⟨P₀,hP₀⟩ :=eventually_atTop.mp hev
  refine ⟨P₀,?_,?_⟩
  · intro p hp hprime a b hb hpb
    haveI : Fact p.Prime :=⟨hprime⟩
    exact twentyMeasureIntPoly_nonvanishing (hP₀ p hp).2.1 (hP₀ p hp).1 a hb hpb
  · intro p hp _
    exact (hP₀ p hp).2.2


theorem refined_atom_point (D : SecondTrialBoundsAt refinedDualTarget) :
    WeightedAtomPointAt refinedDualTarget (538/5) := by
  have hw : ∀ᶠ N : ℕ in atTop, ∀ (k : ℕ) (a : Fin (18*N)),
      |(rowCommonFactor twenty N).eval (CatalanMeasure.chebX (18*N) a)| *
        |restrictedWeight twenty N k (CatalanMeasure.chebX (18*N)) a| ≤
          108000*(N:ℝ)*Real.exp (18*N) :=
    Filter.Eventually.of_forall fun N k a => twenty_full_weight_joint_le N k a
  convert weighted_atom_point_at_target refinedDualTarget D (112/25) (448/5) 18
    refined_first_cost_budget (by norm_num) (by norm_num) hw using 1 <;> norm_num

end
end CatalanMeasure.Parametric
