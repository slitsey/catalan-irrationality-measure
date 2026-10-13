module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow53_checked : contractionList ⟨53,by decide⟩=
    literalEntriesData.getD 53 [] := by decide +kernel
theorem contractionRow53_checked (k : Fin 96) :
    contractionInt ⟨53,by decide⟩ k%1009=literalEntry ⟨53,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow53_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
