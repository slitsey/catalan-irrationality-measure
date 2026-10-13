module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow84_checked : contractionList ⟨84,by decide⟩=
    literalEntriesData.getD 84 [] := by decide +kernel
theorem contractionRow84_checked (k : Fin 96) :
    contractionInt ⟨84,by decide⟩ k%1009=literalEntry ⟨84,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow84_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
