module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow60_checked : contractionList ⟨60,by decide⟩=
    literalEntriesData.getD 60 [] := by decide +kernel
theorem contractionRow60_checked (k : Fin 96) :
    contractionInt ⟨60,by decide⟩ k%1009=literalEntry ⟨60,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow60_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
