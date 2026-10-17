module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow1_checked : contractionList ⟨1,by decide⟩=
    literalEntriesData.getD 1 [] := by decide +kernel
theorem contractionRow1_checked (k : Fin 96) :
    contractionInt ⟨1,by decide⟩ k%1009=literalEntry ⟨1,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow1_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
