module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow76_checked : contractionList ⟨76,by decide⟩=
    literalEntriesData.getD 76 [] := by decide +kernel
theorem contractionRow76_checked (k : Fin 96) :
    contractionInt ⟨76,by decide⟩ k%1009=literalEntry ⟨76,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow76_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
