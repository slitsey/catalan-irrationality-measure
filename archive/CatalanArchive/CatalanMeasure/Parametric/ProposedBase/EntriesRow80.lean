module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow80_checked : contractionList ⟨80,by decide⟩=
    literalEntriesData.getD 80 [] := by decide +kernel
theorem contractionRow80_checked (k : Fin 96) :
    contractionInt ⟨80,by decide⟩ k%1009=literalEntry ⟨80,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow80_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
