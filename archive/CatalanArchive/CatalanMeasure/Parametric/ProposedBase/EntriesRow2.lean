module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow2_checked : contractionList ⟨2,by decide⟩=
    literalEntriesData.getD 2 [] := by decide +kernel
theorem contractionRow2_checked (k : Fin 96) :
    contractionInt ⟨2,by decide⟩ k%1009=literalEntry ⟨2,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow2_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
