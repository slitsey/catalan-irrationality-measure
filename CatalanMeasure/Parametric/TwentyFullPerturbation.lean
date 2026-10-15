module

public import CatalanMeasure.Parametric.TwentyFullAtomDeterminants
public import CatalanMeasure.Parametric.TwentyPerturbationSetup
public import CatalanMeasure.Parametric.TwentyPrefactor

@[expose] public section

namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Filter Polynomial Finset
open scoped BigOperators Topology
noncomputable section

/-- At the critical radius the joint binomial factor has logarithm O(N log N).
It need not be bounded by a constant: its whole quadratic-scale cost vanishes. -/
theorem twenty_full_joint_factor_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ δ : ℝ, |δ| ≤ Real.exp (-(108*(N : ℝ))) →
      (1+(18*N : ℕ)*(|δ| * twentyFullAtomColumnCost N))^(twenty.n N) ≤
        Real.exp (ε*(20*(N : ℝ))^2) := by
  have hh := positive_polynomial_factor_eventually (9720001 : ℝ) (by norm_num) 2
    (ε := 20*ε) (by positivity)
  filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hpoly hN δ hδ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have he : |δ| * Real.exp (108*(N : ℝ)) ≤ 1 := by
    calc
      _ ≤ Real.exp (-(108*(N : ℝ))) * Real.exp (108*(N : ℝ)) :=
        mul_le_mul_of_nonneg_right hδ (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; simp
  have hin : 1+(18*N : ℕ)*(|δ| * twentyFullAtomColumnCost N) ≤
      Real.exp (20*ε*(N : ℝ)) := by
    calc
      _ = 1+9720000*(N : ℝ)^2*(|δ| * Real.exp (108*(N : ℝ))) := by
        unfold twentyFullAtomColumnCost
        push_cast
        ring
      _ ≤ 1+9720000*(N : ℝ)^2 := by
        nlinarith only [mul_le_mul_of_nonneg_left he
          (by positivity : (0 : ℝ) ≤ 9720000*(N : ℝ)^2)]
      _ ≤ 9720001*(N : ℝ)^2 := by nlinarith only [hN1]
      _ ≤ _ := hpoly
  calc
    _ ≤ (Real.exp (20*ε*(N : ℝ)))^(twenty.n N) :=
      pow_le_pow_left₀ (by unfold twentyFullAtomColumnCost; positivity) hin _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      change ((20*N : ℕ) : ℝ)*(20*ε*(N : ℝ)) = ε*(20*(N : ℝ))^2
      push_cast
      ring

theorem twenty_full_perturbation {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x-catalan| ≤ Real.exp (-(108*(N : ℝ))) →
      |aeval x (deltaPoly twenty N)-aeval catalan (deltaPoly twenty N)| ≤
        Real.exp ((20*(N : ℝ))^2*(-twentyDualTarget+Real.log 2/2+ε)) := by
  filter_upwards [twenty_weighted_full_atomMatrix_det_eventually
      (show 0 < ε/3 by positivity),
    twenty_sheet_prefactor_eventually (show 0 < ε/3 by positivity),
    twenty_full_joint_factor_eventually (show 0 < ε/3 by positivity),
    eventually_gt_atTop (0 : ℕ)] with N hd hp hf hN x hx
  let δ : ℝ := x-catalan
  let M : ℝ := twentyAtomBaseBound N (ε/3)
  let c : ℝ := twentyFullAtomColumnCost N
  have hM : 0 ≤ M := by unfold M twentyAtomBaseBound twentySheetPrefactor; positivity
  have hc : 0 ≤ c := by unfold c twentyFullAtomColumnCost; positivity
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
        Real.exp ((20*(N : ℝ))^2*(-twentyDualTarget+Real.log 2/2+ε/3)))*
          Real.exp (ε/3*(20*(N : ℝ))^2) := by
      unfold M twentyAtomBaseBound
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end
end CatalanMeasure.Parametric
