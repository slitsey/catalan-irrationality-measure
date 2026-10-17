module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow17_checked : contractionList ⟨17,by decide⟩=
    literalEntriesData.getD 17 [] := by decide +kernel
theorem contractionRow17_checked (k : Fin 96) :
    contractionInt ⟨17,by decide⟩ k%1009=literalEntry ⟨17,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow17_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
