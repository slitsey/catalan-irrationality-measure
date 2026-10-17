module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow50_checked : contractionList ⟨50,by decide⟩=
    literalEntriesData.getD 50 [] := by decide +kernel
theorem contractionRow50_checked (k : Fin 96) :
    contractionInt ⟨50,by decide⟩ k%1009=literalEntry ⟨50,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow50_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
