module
public import CatalanMeasure.Parametric.ProposedBase.ListContractions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem contractionListRow75_checked : contractionList ⟨75,by decide⟩=
    literalEntriesData.getD 75 [] := by decide +kernel
theorem contractionRow75_checked (k : Fin 96) :
    contractionInt ⟨75,by decide⟩ k%1009=literalEntry ⟨75,by decide⟩ k := by
  rw [← contractionList_getD,contractionListRow75_checked]
  rfl
end CatalanMeasure.Parametric.ProposedBase
