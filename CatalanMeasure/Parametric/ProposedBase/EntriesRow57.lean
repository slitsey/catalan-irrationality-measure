module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow57_checked : contractionList ⟨57,by decide⟩=
    literalEntriesData.getD 57 [] := by decide +kernel
theorem contractionRow57_checked (k : Fin 96) :
    contractionInt ⟨57,by decide⟩ k%1009=literalEntry ⟨57,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow57_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
