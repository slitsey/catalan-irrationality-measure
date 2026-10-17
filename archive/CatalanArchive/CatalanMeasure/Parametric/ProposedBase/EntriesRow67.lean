module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow67_checked : contractionList ⟨67,by decide⟩=
    literalEntriesData.getD 67 [] := by decide +kernel
theorem contractionRow67_checked (k : Fin 96) :
    contractionInt ⟨67,by decide⟩ k%1009=literalEntry ⟨67,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow67_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
