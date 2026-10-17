module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow88_checked : contractionList ⟨88,by decide⟩=
    literalEntriesData.getD 88 [] := by decide +kernel
theorem contractionRow88_checked (k : Fin 96) :
    contractionInt ⟨88,by decide⟩ k%1009=literalEntry ⟨88,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow88_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
