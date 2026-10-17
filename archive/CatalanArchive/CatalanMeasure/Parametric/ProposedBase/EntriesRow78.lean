module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow78_checked : contractionList ⟨78,by decide⟩=
    literalEntriesData.getD 78 [] := by decide +kernel
theorem contractionRow78_checked (k : Fin 96) :
    contractionInt ⟨78,by decide⟩ k%1009=literalEntry ⟨78,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow78_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
