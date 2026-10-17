module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow93_checked : contractionList ⟨93,by decide⟩=
    literalEntriesData.getD 93 [] := by decide +kernel
theorem contractionRow93_checked (k : Fin 96) :
    contractionInt ⟨93,by decide⟩ k%1009=literalEntry ⟨93,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow93_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
