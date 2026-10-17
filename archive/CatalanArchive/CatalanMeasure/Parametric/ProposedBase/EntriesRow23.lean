module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow23_checked : contractionList ⟨23,by decide⟩=
    literalEntriesData.getD 23 [] := by decide +kernel
theorem contractionRow23_checked (k : Fin 96) :
    contractionInt ⟨23,by decide⟩ k%1009=literalEntry ⟨23,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow23_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
