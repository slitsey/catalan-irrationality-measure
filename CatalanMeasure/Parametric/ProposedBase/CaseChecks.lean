module
public import CatalanMeasure.Parametric.ProposedBase.EntriesData
public import CatalanMeasure.Parametric.ProposedBase.InverseZeroData
public import CatalanMeasure.Parametric.ProposedBase.InversePlusData
public import CatalanMeasure.Parametric.ProposedBase.InverseMinusData
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open Matrix
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
noncomputable def literalCaseInt (sigma : ℤ) (r k : Fin 96) : ℤ :=
  literalEntry r.castSucc k+sigma*literalEntry r.succ k

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem literalCase_zero_checked : ∀ r k : Fin 96,
    literalCaseInt 0 r k%1009=baseZeroInt r k := by
  intro r
  fin_cases r <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem literalCase_plus_checked : ∀ r k : Fin 96,
    literalCaseInt 1 r k%1009=basePlusInt r k := by
  intro r
  fin_cases r <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem literalCase_minus_checked : ∀ r k : Fin 96,
    literalCaseInt (-1) r k%1009=baseMinusInt r k := by
  intro r
  fin_cases r <;> decide +kernel

end CatalanMeasure.Parametric.ProposedBase
