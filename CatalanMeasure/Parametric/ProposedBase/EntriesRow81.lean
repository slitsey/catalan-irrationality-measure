module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow81_checked : contractionList ⟨81,by decide⟩=
    literalEntriesData.getD 81 [] := by decide +kernel
theorem contractionRow81_checked (k : Fin 96) :
    contractionInt ⟨81,by decide⟩ k%1009=literalEntry ⟨81,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow81_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
