module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow91_checked : contractionList ⟨91,by decide⟩=
    literalEntriesData.getD 91 [] := by decide +kernel
theorem contractionRow91_checked (k : Fin 96) :
    contractionInt ⟨91,by decide⟩ k%1009=literalEntry ⟨91,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow91_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
