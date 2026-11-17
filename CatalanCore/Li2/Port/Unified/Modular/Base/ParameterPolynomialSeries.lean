/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/ParameterPolynomialSeries.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Base.ParameterSeries
public import CatalanCore.Li2.Port.Unified.Modular.Base.ParameterShift

set_option backward.privateInPublic true

@[expose] public section

/-! The convergent real series for the entire rational-parameter polynomial
functional. This permits a residue-class dissection without p-adic geometric sums. -/
open Polynomial
open scoped BigOperators
namespace CatalanCore.Li2.Port.Li2
noncomputable section

lemma parameterPolynomialTerm (z : ℚ) (P : ℚ[X]) (m : ℕ) :
    ((z^(m+1)*P.eval ((m:ℚ)+1) : ℚ) : ℝ) =
      ∑ k ∈ P.support, (P.coeff k:ℝ)*((z:ℝ)^(m+1)*((m:ℝ)+1)^k) := by
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  rw [Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun k _ => by ring

theorem summable_parameterPolynomial (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) (P : ℚ[X]) :
    Summable (fun m : ℕ => ((z^(m+1)*P.eval ((m:ℚ)+1) : ℚ) : ℝ)) := by
  simp_rw [parameterPolynomialTerm]
  apply summable_sum
  intro k _
  exact (summable_parameterRealMoment z hz k).mul_left _

theorem parameterG_cast_eq_series (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) (P : ℚ[X]) :
    (parameterG z P:ℝ) =
      ∑' m : ℕ, ((z^(m+1)*P.eval ((m:ℚ)+1) : ℚ) : ℝ) := by
  simp_rw [parameterPolynomialTerm]
  rw [Summable.tsum_finsetSum]
  · simp_rw [tsum_mul_left]
    unfold parameterG Polynomial.sum
    push_cast
    simp_rw [parameterMoment_cast_eq_series z hz]
    rfl
  · intro k _
    exact (summable_parameterRealMoment z hz k).mul_left _

end
end CatalanCore.Li2.Port.Li2

end
