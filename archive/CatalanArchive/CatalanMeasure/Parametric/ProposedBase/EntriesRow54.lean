module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow54_checked : contractionList ⟨54,by decide⟩=
    literalEntriesData.getD 54 [] := by decide +kernel
theorem contractionRow54_checked (k : Fin 96) :
    contractionInt ⟨54,by decide⟩ k%1009=literalEntry ⟨54,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow54_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
