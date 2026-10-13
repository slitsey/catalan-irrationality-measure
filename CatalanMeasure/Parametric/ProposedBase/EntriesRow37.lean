module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow37_checked : contractionList ⟨37,by decide⟩=
    literalEntriesData.getD 37 [] := by decide +kernel
theorem contractionRow37_checked (k : Fin 96) :
    contractionInt ⟨37,by decide⟩ k%1009=literalEntry ⟨37,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow37_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
