module
public import CatalanMeasure.Parametric.RealIntegral
public import CatalanMeasure.Parametric.RestrictedWeights
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset OAI.InternalCatalan
noncomputable section

theorem filteredEntryRat_real_perturbation {P : Parameters} (hP : Admissible P)
    {N r k : ℕ} (hN : 0<N) (hr : r<P.n N) (hk : k<P.n N) (z : ℚ) :
    (filteredEntryRat P z N r k:ℝ)=realEntry P N r k+
      ((z:ℝ)-catalan)*(filteredCatalanCoeffRat P N r k:ℝ) := by
  have hh :=filteredEntry_real_affine hP hN hr hk
  rw [filteredEntryRat_affine]
  push_cast
  linear_combination hh

theorem filteredEntryRat_eq_moment_and_atoms {P : Parameters} (hP : Admissible P)
    {N r k : ℕ} (hN : 0<N) (hr : r<P.n N) (hk : k<P.n N) (z : ℚ)
    {J : ℕ} (hJ : P.n N-P.g N≤J) {τ : Fin J → ℝ}
    (hτ : Function.Injective τ) (hneg : ∀ a,τ a<0) :
    (filteredEntryRat P z N r k:ℝ)=
      (∫ p : ℝ×ℝ,realRowAmplitude P N r p.1*(filteredColumn P N k).eval p.2/(1-p.1*p.2)
        ∂realPlaceMeasure.prod (MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))) +
      ((z:ℝ)-catalan)*∑ a,realRowAmplitude P N r (τ a)*restrictedWeight P N k τ a := by
  rw [filteredEntryRat_real_perturbation hP hN hr hk z,realEntry_eq_realPlace_product,
    filteredCatalanCoeff_restricted_weights hP hN hr hJ hτ hneg]
  congr 2
  apply sum_congr rfl
  intro a _
  rw [realRowAmplitude_of_nonpos P N r (hneg a).le]

end
end CatalanMeasure.Parametric
