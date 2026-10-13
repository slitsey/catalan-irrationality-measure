module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow49_checked : contractionList ⟨49,by decide⟩=
    literalEntriesData.getD 49 [] := by decide +kernel
theorem contractionRow49_checked (k : Fin 96) :
    contractionInt ⟨49,by decide⟩ k%1009=literalEntry ⟨49,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow49_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
