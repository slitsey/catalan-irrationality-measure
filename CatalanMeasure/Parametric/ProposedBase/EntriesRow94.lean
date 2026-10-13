module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow94_checked : contractionList ⟨94,by decide⟩=
    literalEntriesData.getD 94 [] := by decide +kernel
theorem contractionRow94_checked (k : Fin 96) :
    contractionInt ⟨94,by decide⟩ k%1009=literalEntry ⟨94,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow94_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
