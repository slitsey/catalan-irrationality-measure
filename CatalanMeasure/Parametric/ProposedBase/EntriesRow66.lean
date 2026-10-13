module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow66_checked : contractionList ⟨66,by decide⟩=
    literalEntriesData.getD 66 [] := by decide +kernel
theorem contractionRow66_checked (k : Fin 96) :
    contractionInt ⟨66,by decide⟩ k%1009=literalEntry ⟨66,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow66_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
