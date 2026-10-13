module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow74_checked : contractionList ⟨74,by decide⟩=
    literalEntriesData.getD 74 [] := by decide +kernel
theorem contractionRow74_checked (k : Fin 96) :
    contractionInt ⟨74,by decide⟩ k%1009=literalEntry ⟨74,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow74_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
