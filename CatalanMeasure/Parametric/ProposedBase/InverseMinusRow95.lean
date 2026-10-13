module
public import CatalanMeasure.Parametric.ProposedBase.InverseMinusData
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open Matrix Finset
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem inverseMinus_row95_checked : ∀ j : Fin 96,
    (∑ k : Fin 96,baseMinusInt ⟨95,by decide⟩ k * inverseMinusInt k j)%1009 =
      if j.val=95 then (1:ℤ) else 0 := by decide +kernel
end CatalanMeasure.Parametric.ProposedBase
