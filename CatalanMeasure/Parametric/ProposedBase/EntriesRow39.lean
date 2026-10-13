module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow39_checked : contractionList ⟨39,by decide⟩=
    literalEntriesData.getD 39 [] := by decide +kernel
theorem contractionRow39_checked (k : Fin 96) :
    contractionInt ⟨39,by decide⟩ k%1009=literalEntry ⟨39,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow39_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
