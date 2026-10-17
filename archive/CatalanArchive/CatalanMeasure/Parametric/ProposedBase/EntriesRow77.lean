module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow77_checked : contractionList ⟨77,by decide⟩=
    literalEntriesData.getD 77 [] := by decide +kernel
theorem contractionRow77_checked (k : Fin 96) :
    contractionInt ⟨77,by decide⟩ k%1009=literalEntry ⟨77,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow77_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
