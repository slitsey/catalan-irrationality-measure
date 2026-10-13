module
public import CatalanMeasure.Parametric.ProposedBase.InverseZeroData
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open Matrix Finset
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem inverseZero_row22_checked : ∀ j : Fin 96,
    (∑ k : Fin 96,baseZeroInt ⟨22,by decide⟩ k * inverseZeroInt k j)%1009 =
      if j.val=22 then (1:ℤ) else 0 := by decide +kernel
end CatalanMeasure.Parametric.ProposedBase
