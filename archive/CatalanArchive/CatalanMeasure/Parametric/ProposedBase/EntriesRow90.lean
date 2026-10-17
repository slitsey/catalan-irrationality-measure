module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow90_checked : contractionList ⟨90,by decide⟩=
    literalEntriesData.getD 90 [] := by decide +kernel
theorem contractionRow90_checked (k : Fin 96) :
    contractionInt ⟨90,by decide⟩ k%1009=literalEntry ⟨90,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow90_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
