module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow25_checked : contractionList ⟨25,by decide⟩=
    literalEntriesData.getD 25 [] := by decide +kernel
theorem contractionRow25_checked (k : Fin 96) :
    contractionInt ⟨25,by decide⟩ k%1009=literalEntry ⟨25,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow25_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
