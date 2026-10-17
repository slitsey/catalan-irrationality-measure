module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow18_checked : contractionList ⟨18,by decide⟩=
    literalEntriesData.getD 18 [] := by decide +kernel
theorem contractionRow18_checked (k : Fin 96) :
    contractionInt ⟨18,by decide⟩ k%1009=literalEntry ⟨18,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow18_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
