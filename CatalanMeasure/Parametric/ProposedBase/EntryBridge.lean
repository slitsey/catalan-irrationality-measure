module
public import CatalanMeasure.Parametric.ProposedBase.EntriesData
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open OAI.InternalCatalan Finset
noncomputable section

theorem baseFilteredContraction_int (r : Fin 97) (k : Fin 96) :
    baseFilteredContraction proposed 1009 r.val k = (contractionInt r k:ZMod 1009) := by
  have hh : (3/2:ZMod 1009)=(506:ℤ) := by decide +kernel
  rw [baseFilteredContraction_filtered_forms]
  rw [← Fin.sum_univ_eq_sum_range (fun i =>((rowP proposed 1 r.val).coeff i:ZMod 1009)*
    palindromicRatResidue 1009 (filteredMomentRat i k.val))]
  rw [← Fin.sum_univ_eq_sum_range (fun i =>((rowD proposed 1 r.val).coeff i:ZMod 1009)*
    palindromicRatResidue 1009 (filteredZetaRat i k.val))]
  simp_rw [proposedPCoefficients_spec r,proposedDCoefficients_spec r,momentTable_spec k,zetaTable_spec k]
  rw [hh]
  unfold contractionInt
  push_cast
  rfl

end
end CatalanMeasure.Parametric.ProposedBase
