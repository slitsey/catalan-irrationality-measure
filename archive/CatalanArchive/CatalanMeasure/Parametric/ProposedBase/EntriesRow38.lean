module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow38_checked : contractionList ⟨38,by decide⟩=
    literalEntriesData.getD 38 [] := by decide +kernel
theorem contractionRow38_checked (k : Fin 96) :
    contractionInt ⟨38,by decide⟩ k%1009=literalEntry ⟨38,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow38_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
