module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceDigit

/-! Elementary coefficient response of the ordinary trace numerator
`H=x^6 G`. This supplies the complete Frobenius extraction step without
Cartier operators, finite-field extensions, or residues at quadratic roots. -/

@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

theorem secondaryTent_source_frobenius_product_coeff {p : ℕ} [hp : Fact p.Prime]
    (H I : (ZMod p)[X]) (hI : I.natDegree<p) (e : Fin p) (k : ℕ) :
    (H^p*I).coeff (p*k+e.val)=H.coeff k*I.coeff e.val := by
  have hpack : (∑ j : Fin p, (C (I.coeff j.val)*H)^p*X^j.val)=H^p*I := by
    simp only [mul_pow, ← C_pow, ZMod.pow_card]
    conv_rhs => rw [I.as_sum_range_C_mul_X_pow' hI, Finset.mul_sum]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [← hpack, secondaryTent_frobenius_packet_coeff]
  simp [coeff_C_mul, mul_comm]

/-- The coefficient required by the complete actual source trace. The
numerator H may have arbitrary degree; only the input degree is bounded. -/
theorem secondaryTent_source_trace_response_coeff {p e : ℕ} [hp : Fact p.Prime]
    (H I : (ZMod p)[X]) (hI : I.natDegree<p) (he : e<p) :
    (H^p*I).coeff (6*p-1-e)=H.coeff 5*I.coeff (p-1-e) := by
  have hr : p-1-e<p := by omega
  have hidx : 6*p-1-e=p*5+(p-1-e) := by omega
  rw [hidx]
  exact secondaryTent_source_frobenius_product_coeff H I hI ⟨p-1-e,hr⟩ 5

/-- Finite sums of reconstructed inputs have exactly their fixed macro
symbol coefficients as response weights. No rank condition is involved. -/
theorem secondaryTent_source_trace_response_sum {p e : ℕ} [hp : Fact p.Prime]
    {ι : Type*} (s : Finset ι) (H I : ι → (ZMod p)[X])
    (hI : ∀ i∈s, (I i).natDegree<p) (he : e<p) :
    (∑ i∈s, (H i)^p*I i).coeff (6*p-1-e)=
      ∑ i∈s, (H i).coeff 5*(I i).coeff (p-1-e) := by
  rw [finsetSum_coeff]
  exact Finset.sum_congr rfl (fun i hi =>
    secondaryTent_source_trace_response_coeff (H i) (I i) (hI i hi) he)

end
end CatalanMeasure.Parametric
