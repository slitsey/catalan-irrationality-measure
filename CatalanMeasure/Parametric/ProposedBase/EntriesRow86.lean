module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow86_checked : contractionList ⟨86,by decide⟩=
    literalEntriesData.getD 86 [] := by decide +kernel
theorem contractionRow86_checked (k : Fin 96) :
    contractionInt ⟨86,by decide⟩ k%1009=literalEntry ⟨86,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow86_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
