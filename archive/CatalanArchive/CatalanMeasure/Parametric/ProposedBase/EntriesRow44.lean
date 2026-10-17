module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow44_checked : contractionList ⟨44,by decide⟩=
    literalEntriesData.getD 44 [] := by decide +kernel
theorem contractionRow44_checked (k : Fin 96) :
    contractionInt ⟨44,by decide⟩ k%1009=literalEntry ⟨44,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow44_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
