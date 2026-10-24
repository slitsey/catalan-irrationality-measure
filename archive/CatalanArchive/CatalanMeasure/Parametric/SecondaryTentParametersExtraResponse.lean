module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentParametersGeometry
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

/-- The extra physical J=4 block is already paid as an actual response
constraint, with the same polynomial used on every other raw column. -/
theorem secondaryTent_negative_extra_raw_response {p N half g d a b e : ℕ} [Fact p.Prime]
    (he : e<4*d)
    (v : LinearMap.ker (secondaryTentConstraintMap (secondaryTentNegativeCosts N p half g d)
      (secondaryTentNegativeParameterConstraints p N half g d a b))) :
    (∑ r : Fin (20*N), palindromicRatResidue p
      ((p:ℚ)^2*rawEntryRat twenty 0 N r.val (4*p+e))*
        secondaryTentNegativeActualRowLinear p N half g d a b v r) =
      (secondaryTentParameterResponsePolynomialLinear p N g 0 v.val).eval ((4*p+e:ℕ):ZMod p) := by
  have hf := secondaryTent_constraint_kernel_flag _
    (secondaryTentNegativeParameterConstraints p N half g d a b) v 5
  have hh := congrFun hf (⟨e,he⟩ : Fin (4*d))
  change (∑ r : Fin (20*N), palindromicRatResidue p
    ((p:ℚ)^2*rawEntryRat twenty 0 N r.val (4*p+e))*
      secondaryTentParameterActualRowLinear p N g 0 a b v.val r) -
        (secondaryTentParameterResponsePolynomialLinear p N g 0 v.val).eval (e:ZMod p)=0 at hh
  have hc : ((4*p+e:ℕ):ZMod p)=(e:ZMod p) := by simp
  rw [hc]
  exact sub_eq_zero.mp hh

end
end CatalanMeasure.Parametric
