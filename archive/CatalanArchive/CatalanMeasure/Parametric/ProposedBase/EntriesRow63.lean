module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow63_checked : contractionList ⟨63,by decide⟩=
    literalEntriesData.getD 63 [] := by decide +kernel
theorem contractionRow63_checked (k : Fin 96) :
    contractionInt ⟨63,by decide⟩ k%1009=literalEntry ⟨63,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow63_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
