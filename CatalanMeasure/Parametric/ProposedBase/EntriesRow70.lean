module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow70_checked : contractionList ⟨70,by decide⟩=
    literalEntriesData.getD 70 [] := by decide +kernel
theorem contractionRow70_checked (k : Fin 96) :
    contractionInt ⟨70,by decide⟩ k%1009=literalEntry ⟨70,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow70_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
