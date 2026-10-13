module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow15_checked : contractionList ⟨15,by decide⟩=
    literalEntriesData.getD 15 [] := by decide +kernel
theorem contractionRow15_checked (k : Fin 96) :
    contractionInt ⟨15,by decide⟩ k%1009=literalEntry ⟨15,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow15_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
