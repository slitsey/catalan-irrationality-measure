module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow52_checked : contractionList ⟨52,by decide⟩=
    literalEntriesData.getD 52 [] := by decide +kernel
theorem contractionRow52_checked (k : Fin 96) :
    contractionInt ⟨52,by decide⟩ k%1009=literalEntry ⟨52,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow52_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
