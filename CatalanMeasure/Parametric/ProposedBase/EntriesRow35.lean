module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow35_checked : contractionList ⟨35,by decide⟩=
    literalEntriesData.getD 35 [] := by decide +kernel
theorem contractionRow35_checked (k : Fin 96) :
    contractionInt ⟨35,by decide⟩ k%1009=literalEntry ⟨35,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow35_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
