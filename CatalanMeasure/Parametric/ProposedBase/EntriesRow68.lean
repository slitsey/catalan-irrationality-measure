module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow68_checked : contractionList ⟨68,by decide⟩=
    literalEntriesData.getD 68 [] := by decide +kernel
theorem contractionRow68_checked (k : Fin 96) :
    contractionInt ⟨68,by decide⟩ k%1009=literalEntry ⟨68,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow68_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
