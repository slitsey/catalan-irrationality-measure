module
public import CatalanMeasure.Parametric.ProposedBase.InversePlusData
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open Matrix Finset
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem inversePlus_row59_checked : ∀ j : Fin 96,
    (∑ k : Fin 96,basePlusInt ⟨59,by decide⟩ k * inversePlusInt k j)%1009 =
      if j.val=59 then (1:ℤ) else 0 := by decide +kernel
end CatalanMeasure.Parametric.ProposedBase
