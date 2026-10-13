module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow48_checked : contractionList ⟨48,by decide⟩=
    literalEntriesData.getD 48 [] := by decide +kernel
theorem contractionRow48_checked (k : Fin 96) :
    contractionInt ⟨48,by decide⟩ k%1009=literalEntry ⟨48,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow48_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
