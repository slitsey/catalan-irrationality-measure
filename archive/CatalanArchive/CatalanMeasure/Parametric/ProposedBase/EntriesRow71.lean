module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow71_checked : contractionList ⟨71,by decide⟩=
    literalEntriesData.getD 71 [] := by decide +kernel
theorem contractionRow71_checked (k : Fin 96) :
    contractionInt ⟨71,by decide⟩ k%1009=literalEntry ⟨71,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow71_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
