module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow96_checked : contractionList ⟨96,by decide⟩=
    literalEntriesData.getD 96 [] := by decide +kernel
theorem contractionRow96_checked (k : Fin 96) :
    contractionInt ⟨96,by decide⟩ k%1009=literalEntry ⟨96,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow96_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
