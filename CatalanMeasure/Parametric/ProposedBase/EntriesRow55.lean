module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow55_checked : contractionList ⟨55,by decide⟩=
    literalEntriesData.getD 55 [] := by decide +kernel
theorem contractionRow55_checked (k : Fin 96) :
    contractionInt ⟨55,by decide⟩ k%1009=literalEntry ⟨55,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow55_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
