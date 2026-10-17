module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow11_checked : contractionList ⟨11,by decide⟩=
    literalEntriesData.getD 11 [] := by decide +kernel
theorem contractionRow11_checked (k : Fin 96) :
    contractionInt ⟨11,by decide⟩ k%1009=literalEntry ⟨11,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow11_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
