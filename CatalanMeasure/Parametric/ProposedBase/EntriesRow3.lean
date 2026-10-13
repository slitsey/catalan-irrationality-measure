module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow3_checked : contractionList ⟨3,by decide⟩=
    literalEntriesData.getD 3 [] := by decide +kernel
theorem contractionRow3_checked (k : Fin 96) :
    contractionInt ⟨3,by decide⟩ k%1009=literalEntry ⟨3,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow3_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
