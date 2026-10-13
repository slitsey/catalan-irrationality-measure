module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow51_checked : contractionList ⟨51,by decide⟩=
    literalEntriesData.getD 51 [] := by decide +kernel
theorem contractionRow51_checked (k : Fin 96) :
    contractionInt ⟨51,by decide⟩ k%1009=literalEntry ⟨51,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow51_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
