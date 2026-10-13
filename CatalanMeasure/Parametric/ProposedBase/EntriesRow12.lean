module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow12_checked : contractionList ⟨12,by decide⟩=
    literalEntriesData.getD 12 [] := by decide +kernel
theorem contractionRow12_checked (k : Fin 96) :
    contractionInt ⟨12,by decide⟩ k%1009=literalEntry ⟨12,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow12_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
