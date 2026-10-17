module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow24_checked : contractionList ⟨24,by decide⟩=
    literalEntriesData.getD 24 [] := by decide +kernel
theorem contractionRow24_checked (k : Fin 96) :
    contractionInt ⟨24,by decide⟩ k%1009=literalEntry ⟨24,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow24_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
