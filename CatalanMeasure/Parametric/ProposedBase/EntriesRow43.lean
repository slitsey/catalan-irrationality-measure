module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow43_checked : contractionList ⟨43,by decide⟩=
    literalEntriesData.getD 43 [] := by decide +kernel
theorem contractionRow43_checked (k : Fin 96) :
    contractionInt ⟨43,by decide⟩ k%1009=literalEntry ⟨43,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow43_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
