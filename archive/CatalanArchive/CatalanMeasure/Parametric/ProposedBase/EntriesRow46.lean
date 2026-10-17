module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow46_checked : contractionList ⟨46,by decide⟩=
    literalEntriesData.getD 46 [] := by decide +kernel
theorem contractionRow46_checked (k : Fin 96) :
    contractionInt ⟨46,by decide⟩ k%1009=literalEntry ⟨46,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow46_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
