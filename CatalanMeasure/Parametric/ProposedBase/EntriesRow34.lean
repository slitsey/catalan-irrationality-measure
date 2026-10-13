module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow34_checked : contractionList ⟨34,by decide⟩=
    literalEntriesData.getD 34 [] := by decide +kernel
theorem contractionRow34_checked (k : Fin 96) :
    contractionInt ⟨34,by decide⟩ k%1009=literalEntry ⟨34,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow34_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
