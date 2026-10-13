module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow19_checked : contractionList ⟨19,by decide⟩=
    literalEntriesData.getD 19 [] := by decide +kernel
theorem contractionRow19_checked (k : Fin 96) :
    contractionInt ⟨19,by decide⟩ k%1009=literalEntry ⟨19,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow19_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
