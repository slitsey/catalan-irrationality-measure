module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow95_checked : contractionList ⟨95,by decide⟩=
    literalEntriesData.getD 95 [] := by decide +kernel
theorem contractionRow95_checked (k : Fin 96) :
    contractionInt ⟨95,by decide⟩ k%1009=literalEntry ⟨95,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow95_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
