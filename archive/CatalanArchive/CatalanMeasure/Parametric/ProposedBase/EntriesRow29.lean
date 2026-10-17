module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow29_checked : contractionList ⟨29,by decide⟩=
    literalEntriesData.getD 29 [] := by decide +kernel
theorem contractionRow29_checked (k : Fin 96) :
    contractionInt ⟨29,by decide⟩ k%1009=literalEntry ⟨29,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow29_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
