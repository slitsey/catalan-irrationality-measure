module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow36_checked : contractionList ⟨36,by decide⟩=
    literalEntriesData.getD 36 [] := by decide +kernel
theorem contractionRow36_checked (k : Fin 96) :
    contractionInt ⟨36,by decide⟩ k%1009=literalEntry ⟨36,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow36_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
