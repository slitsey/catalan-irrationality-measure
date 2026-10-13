module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow6_checked : contractionList ⟨6,by decide⟩=
    literalEntriesData.getD 6 [] := by decide +kernel
theorem contractionRow6_checked (k : Fin 96) :
    contractionInt ⟨6,by decide⟩ k%1009=literalEntry ⟨6,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow6_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
