module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow32_checked : contractionList ⟨32,by decide⟩=
    literalEntriesData.getD 32 [] := by decide +kernel
theorem contractionRow32_checked (k : Fin 96) :
    contractionInt ⟨32,by decide⟩ k%1009=literalEntry ⟨32,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow32_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
