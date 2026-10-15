module
public import CatalanMeasure.Parametric.SecondaryTentSourceTraceFrobenius

/-! The signed natural row packets give the ordinary trace numerator. -/
@[expose] public section
namespace CatalanMeasure.Parametric
noncomputable section

theorem secondaryTent_source_trace_basis_factors {K : Type*} [Field K]
    (x s A B : K) (hs : s≠0) :
    secondaryTentSourceTraceTerm x s A B (1/(2*x)) 0 =
      ((x-1+s)/(16*x^4)/(2*x*s))*(B-s*A/x) ∧
    secondaryTentSourceTraceTerm x s A B 0 (1/(2*x*(x-1))) =
      ((x-1+s)/(16*x^4)/(2*x*(x-1)))*(B-s*A/x) := by
  constructor <;> unfold secondaryTentSourceTraceTerm
  · ring
  · simp only [zero_add]
    field_simp [hs]
    <;> ring

theorem secondaryTent_source_weighted_natural_trace {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (x s A B HU HV h u v : K)
    (h2 : (2:K)≠0) (hx : x≠0) (hs : s≠0) (hw : x-1≠0)
    (hcurve : s^2=x^2-1)
    (hu : u*h = 8*s*
      ((((x-1+s)/(16*x^4)/(2*x*s))^p)*HU +
       (((x-1+s)/(16*x^4)/(2*x*(x-1)))^p)*HV))
    (hv : v*h = 8*(-s)*
      ((((x-1-s)/(16*x^4)/(2*x*(-s)))^p)*HU +
       (((x-1-s)/(16*x^4)/(2*x*(x-1)))^p)*HV)) :
    h*(u*(B-s*A/x)^p-v*(B+s*A/x)^p) =
      8*s*(((x*B-(x-1)*A)^p*HU+(x*B-(x+1)*A)^p*HV)/16)/x^(6*p) := by
  have ht := secondaryTent_source_natural_mirror_frobenius
    x s A B HU HV h2 hx hs hw hcurve
  obtain ⟨hP,hQ⟩ := secondaryTent_source_trace_basis_factors x s A B hs
  obtain ⟨hmP,hmQ⟩ := secondaryTent_source_trace_basis_factors x (-s) A B (neg_ne_zero.mpr hs)
  rw [hP,hQ,hmP,hmQ] at ht
  simp only [mul_pow, sub_neg_eq_add, neg_mul, neg_div, sub_eq_add_neg] at ht hu hv ⊢
  calc
    _ = (u*h)*(B + -(s*A/x))^p - (v*h)*(B+s*A/x)^p := by ring
    _ = _ := by rw [hu,hv]; linear_combination ht

end
end CatalanMeasure.Parametric
