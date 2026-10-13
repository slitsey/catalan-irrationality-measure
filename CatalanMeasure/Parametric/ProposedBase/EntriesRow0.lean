module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow0_checked : contractionList ⟨0,by decide⟩=
    literalEntriesData.getD 0 [] := by decide +kernel
theorem contractionRow0_checked (k : Fin 96) :
    contractionInt ⟨0,by decide⟩ k%1009=literalEntry ⟨0,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow0_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
