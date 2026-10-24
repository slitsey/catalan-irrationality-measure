module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceResponse
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceModularTrace

/-! The natural combined numerator has exactly the fixed trace responses,
before any source/row denominator bookkeeping. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

def secondaryTentSourceNaturalSymbol (p J : ℕ) [Fact p.Prime]
    (HU HV : (ZMod p)[X]) : (ZMod p)[X] :=
  C (1/16:ZMod p)*
    ((X*secondaryTentSourceZetaForward p J-(X-1)*secondaryTentSourceMomentForward p J)^p*HU +
     (X*secondaryTentSourceZetaForward p J-(X+1)*secondaryTentSourceMomentForward p J)^p*HV)

theorem secondaryTent_source_natural_frobenius_sum {p : ℕ} [Fact p.Prime]
    {ι : Type*} (s : Finset ι) (A B : (ZMod p)[X]) (P Q I : ι → (ZMod p)[X]) :
    (∑ i∈s, (secondaryTentSourceTraceNumerator A B (P i) (Q i))^p*I i) =
      C (1/16:ZMod p)*
        ((X*B-(X-1)*A)^p*(∑ i∈s, (P i)^p*I i) +
         (X*B-(X+1)*A)^p*(∑ i∈s, (Q i)^p*I i)) := by
  simp only [secondaryTentSourceTraceNumerator, mul_pow, add_pow_char,
    ← C_pow, ZMod.pow_card]
  simp only [mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem secondaryTent_source_natural_response {p e J : ℕ} [Fact p.Prime]
    {ι : Type*} (s : Finset ι) (c : ι → (Fin 7 → ZMod p))
    (I : ι → (ZMod p)[X]) (hI : ∀ i∈s, (I i).natDegree<p) (he : e<p) :
    (C (1/16:ZMod p)*
      ((X*secondaryTentSourceZetaForward p J-(X-1)*secondaryTentSourceMomentForward p J)^p*
        (∑ i∈s, (secondaryTentRowNaturalP (c i))^p*I i) +
       (X*secondaryTentSourceZetaForward p J-(X+1)*secondaryTentSourceMomentForward p J)^p*
        (∑ i∈s, (secondaryTentRowNaturalQ (c i))^p*I i))).coeff (6*p-1-e) =
      ∑ i∈s, (secondaryTentSourceMacroTrace p J (c i)).coeff 5*(I i).coeff (p-1-e) := by
  rw [← secondaryTent_source_natural_frobenius_sum]
  exact secondaryTent_source_trace_response_sum s
    (fun i => secondaryTentSourceMacroTrace p J (c i)) I hI he

theorem secondaryTent_source_fixed_natural_response {p e : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ 6310886697782126553600) (J : Fin 4)
    (I : Fin 5 → (ZMod p)[X]) (hI : ∀ i, (I i).natDegree<p) (he : e<p) :
    (secondaryTentSourceNaturalSymbol p J.val
      (∑ i : Fin 5,
        (secondaryTentRowNaturalP (fun k => (secondaryTentSeedCoefficients k i:ZMod p)))^p*I i)
      (∑ i : Fin 5,
        (secondaryTentRowNaturalQ (fun k => (secondaryTentSeedCoefficients k i:ZMod p)))^p*I i)).coeff
          (6*p-1-e) =
      ∑ i : Fin 5, (secondaryTentSourceFixedResponseInteger J i:ZMod p)*(I i).coeff (p-1-e) := by
  unfold secondaryTentSourceNaturalSymbol
  rw [secondaryTent_source_natural_response Finset.univ
    (fun i : Fin 5 => fun k => (secondaryTentSeedCoefficients k i:ZMod p)) I
    (fun i hi => hI i) he]
  apply Finset.sum_congr rfl
  intro i hi
  rw [secondaryTent_source_fixed_macro_modular hp J i]

end
end CatalanMeasure.Parametric
