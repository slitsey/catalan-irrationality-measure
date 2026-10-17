module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow26_checked : contractionList ⟨26,by decide⟩=
    literalEntriesData.getD 26 [] := by decide +kernel
theorem contractionRow26_checked (k : Fin 96) :
    contractionInt ⟨26,by decide⟩ k%1009=literalEntry ⟨26,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow26_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
