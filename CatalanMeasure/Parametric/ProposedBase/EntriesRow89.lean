module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow89_checked : contractionList ⟨89,by decide⟩=
    literalEntriesData.getD 89 [] := by decide +kernel
theorem contractionRow89_checked (k : Fin 96) :
    contractionInt ⟨89,by decide⟩ k%1009=literalEntry ⟨89,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow89_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
