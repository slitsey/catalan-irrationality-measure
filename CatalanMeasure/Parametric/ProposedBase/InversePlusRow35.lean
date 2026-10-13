module
public import CatalanMeasure.Parametric.ProposedBase.InversePlusData
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open Matrix Finset
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem inversePlus_row35_checked : ∀ j : Fin 96,
    (∑ k : Fin 96,basePlusInt ⟨35,by decide⟩ k * inversePlusInt k j)%1009 =
      if j.val=35 then (1:ℤ) else 0 := by decide +kernel
end CatalanMeasure.Parametric.ProposedBase
