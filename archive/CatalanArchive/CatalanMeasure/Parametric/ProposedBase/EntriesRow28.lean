module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow28_checked : contractionList ⟨28,by decide⟩=
    literalEntriesData.getD 28 [] := by decide +kernel
theorem contractionRow28_checked (k : Fin 96) :
    contractionInt ⟨28,by decide⟩ k%1009=literalEntry ⟨28,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow28_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
