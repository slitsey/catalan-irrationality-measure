module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow27_checked : contractionList ⟨27,by decide⟩=
    literalEntriesData.getD 27 [] := by decide +kernel
theorem contractionRow27_checked (k : Fin 96) :
    contractionInt ⟨27,by decide⟩ k%1009=literalEntry ⟨27,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow27_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
