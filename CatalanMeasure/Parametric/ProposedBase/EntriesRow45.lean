module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow45_checked : contractionList ⟨45,by decide⟩=
    literalEntriesData.getD 45 [] := by decide +kernel
theorem contractionRow45_checked (k : Fin 96) :
    contractionInt ⟨45,by decide⟩ k%1009=literalEntry ⟨45,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow45_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
