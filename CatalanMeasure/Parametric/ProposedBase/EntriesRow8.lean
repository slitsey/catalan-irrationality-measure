module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow8_checked : contractionList ⟨8,by decide⟩=
    literalEntriesData.getD 8 [] := by decide +kernel
theorem contractionRow8_checked (k : Fin 96) :
    contractionInt ⟨8,by decide⟩ k%1009=literalEntry ⟨8,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow8_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
