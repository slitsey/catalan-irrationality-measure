module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow13_checked : contractionList ⟨13,by decide⟩=
    literalEntriesData.getD 13 [] := by decide +kernel
theorem contractionRow13_checked (k : Fin 96) :
    contractionInt ⟨13,by decide⟩ k%1009=literalEntry ⟨13,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow13_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
