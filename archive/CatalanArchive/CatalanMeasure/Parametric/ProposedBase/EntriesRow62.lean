module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow62_checked : contractionList ⟨62,by decide⟩=
    literalEntriesData.getD 62 [] := by decide +kernel
theorem contractionRow62_checked (k : Fin 96) :
    contractionInt ⟨62,by decide⟩ k%1009=literalEntry ⟨62,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow62_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
