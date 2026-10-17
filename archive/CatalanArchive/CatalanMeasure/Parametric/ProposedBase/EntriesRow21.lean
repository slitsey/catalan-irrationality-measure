module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow21_checked : contractionList ⟨21,by decide⟩=
    literalEntriesData.getD 21 [] := by decide +kernel
theorem contractionRow21_checked (k : Fin 96) :
    contractionInt ⟨21,by decide⟩ k%1009=literalEntry ⟨21,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow21_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
