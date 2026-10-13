module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow59_checked : contractionList ⟨59,by decide⟩=
    literalEntriesData.getD 59 [] := by decide +kernel
theorem contractionRow59_checked (k : Fin 96) :
    contractionInt ⟨59,by decide⟩ k%1009=literalEntry ⟨59,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow59_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
