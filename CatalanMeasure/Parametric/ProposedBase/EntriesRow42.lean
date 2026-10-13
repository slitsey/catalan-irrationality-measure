module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow42_checked : contractionList ⟨42,by decide⟩=
    literalEntriesData.getD 42 [] := by decide +kernel
theorem contractionRow42_checked (k : Fin 96) :
    contractionInt ⟨42,by decide⟩ k%1009=literalEntry ⟨42,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow42_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
