module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow58_checked : contractionList ⟨58,by decide⟩=
    literalEntriesData.getD 58 [] := by decide +kernel
theorem contractionRow58_checked (k : Fin 96) :
    contractionInt ⟨58,by decide⟩ k%1009=literalEntry ⟨58,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow58_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
