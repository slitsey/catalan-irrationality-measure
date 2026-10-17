module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow85_checked : contractionList ⟨85,by decide⟩=
    literalEntriesData.getD 85 [] := by decide +kernel
theorem contractionRow85_checked (k : Fin 96) :
    contractionInt ⟨85,by decide⟩ k%1009=literalEntry ⟨85,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow85_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
