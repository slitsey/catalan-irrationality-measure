module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow92_checked : contractionList ⟨92,by decide⟩=
    literalEntriesData.getD 92 [] := by decide +kernel
theorem contractionRow92_checked (k : Fin 96) :
    contractionInt ⟨92,by decide⟩ k%1009=literalEntry ⟨92,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow92_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
