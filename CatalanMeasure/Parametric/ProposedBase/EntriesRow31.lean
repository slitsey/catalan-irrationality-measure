module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow31_checked : contractionList ⟨31,by decide⟩=
    literalEntriesData.getD 31 [] := by decide +kernel
theorem contractionRow31_checked (k : Fin 96) :
    contractionInt ⟨31,by decide⟩ k%1009=literalEntry ⟨31,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow31_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
