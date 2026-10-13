module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow83_checked : contractionList ⟨83,by decide⟩=
    literalEntriesData.getD 83 [] := by decide +kernel
theorem contractionRow83_checked (k : Fin 96) :
    contractionInt ⟨83,by decide⟩ k%1009=literalEntry ⟨83,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow83_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
