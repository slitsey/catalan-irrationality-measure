module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow5_checked : contractionList ⟨5,by decide⟩=
    literalEntriesData.getD 5 [] := by decide +kernel
theorem contractionRow5_checked (k : Fin 96) :
    contractionInt ⟨5,by decide⟩ k%1009=literalEntry ⟨5,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow5_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
