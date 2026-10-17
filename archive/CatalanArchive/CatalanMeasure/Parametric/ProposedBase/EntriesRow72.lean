module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow72_checked : contractionList ⟨72,by decide⟩=
    literalEntriesData.getD 72 [] := by decide +kernel
theorem contractionRow72_checked (k : Fin 96) :
    contractionInt ⟨72,by decide⟩ k%1009=literalEntry ⟨72,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow72_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
