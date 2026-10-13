module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow82_checked : contractionList ⟨82,by decide⟩=
    literalEntriesData.getD 82 [] := by decide +kernel
theorem contractionRow82_checked (k : Fin 96) :
    contractionInt ⟨82,by decide⟩ k%1009=literalEntry ⟨82,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow82_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
