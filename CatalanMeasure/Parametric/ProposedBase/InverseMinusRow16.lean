module
public import CatalanMeasure.Parametric.ProposedBase.InverseMinusData
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open Matrix Finset
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem inverseMinus_row16_checked : ∀ j : Fin 96,
    (∑ k : Fin 96,baseMinusInt ⟨16,by decide⟩ k * inverseMinusInt k j)%1009 =
      if j.val=16 then (1:ℤ) else 0 := by decide +kernel
end CatalanMeasure.Parametric.ProposedBase
