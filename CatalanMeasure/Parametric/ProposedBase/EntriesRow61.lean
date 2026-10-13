module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow61_checked : contractionList ⟨61,by decide⟩=
    literalEntriesData.getD 61 [] := by decide +kernel
theorem contractionRow61_checked (k : Fin 96) :
    contractionInt ⟨61,by decide⟩ k%1009=literalEntry ⟨61,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow61_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
