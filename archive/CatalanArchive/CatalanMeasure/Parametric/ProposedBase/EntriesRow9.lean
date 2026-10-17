module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow9_checked : contractionList ⟨9,by decide⟩=
    literalEntriesData.getD 9 [] := by decide +kernel
theorem contractionRow9_checked (k : Fin 96) :
    contractionInt ⟨9,by decide⟩ k%1009=literalEntry ⟨9,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow9_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
