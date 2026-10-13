module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow64_checked : contractionList ⟨64,by decide⟩=
    literalEntriesData.getD 64 [] := by decide +kernel
theorem contractionRow64_checked (k : Fin 96) :
    contractionInt ⟨64,by decide⟩ k%1009=literalEntry ⟨64,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow64_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
