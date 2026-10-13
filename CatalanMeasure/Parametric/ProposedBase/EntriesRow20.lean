module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow20_checked : contractionList ⟨20,by decide⟩=
    literalEntriesData.getD 20 [] := by decide +kernel
theorem contractionRow20_checked (k : Fin 96) :
    contractionInt ⟨20,by decide⟩ k%1009=literalEntry ⟨20,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow20_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
