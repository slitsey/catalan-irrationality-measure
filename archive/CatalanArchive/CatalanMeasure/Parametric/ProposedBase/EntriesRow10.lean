module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow10_checked : contractionList ⟨10,by decide⟩=
    literalEntriesData.getD 10 [] := by decide +kernel
theorem contractionRow10_checked (k : Fin 96) :
    contractionInt ⟨10,by decide⟩ k%1009=literalEntry ⟨10,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow10_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
