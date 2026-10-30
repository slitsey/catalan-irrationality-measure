import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 6aeac1b3cd3b134e710a387d659d62434c0958e218c6fd26165eacf2e7a4e169, root class 3. -/
def C3T14 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 5) | 2 => (-29 / 60) | 3 => (-197 / 380) | 4 => (-664 / 1235) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24 / 25) | 2 => (-3781 / 3600) | 3 => (-465647 / 433200) | 4 => (-9928171 / 9151350) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-411709889794699 / 694156807447285) | 4, 1 => (-12879997371908 / 59499154924053) | 4, 2 => (-18175607642096 / 138831361489457) | 4, 3 => (-684354583296 / 7306913762603) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (411709889794699 / 694156807447285) | 4, 1 => (12879997371908 / 59499154924053) | 4, 2 => (18175607642096 / 138831361489457) | 4, 3 => (684354583296 / 7306913762603) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C3T14_ok : C3T14.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T14_den : ℕ := 2082470422341855
theorem C3T14_den_ok :
    (∀ d ∈ C3T14.R, ∀ e ∈ C3T14.R, (C3T14.Lq d e).den ∣ C3T14_den ∧ (C3T14.Lq' d e).den ∣ C3T14_den) ∧
    (∀ d ∈ C3T14.C, ∀ e ∈ C3T14.C, (C3T14.Pq d e).den ∣ C3T14_den ∧ (C3T14.Pq' d e).den ∣ C3T14_den) := by
  constructor <;> decide +kernel
theorem C3T14_rload_4 : C3T14.rload 4 = ((-71134325929822 / 2082470422341855), (-141287501650532 / 416494084468371)) := by decide +kernel
#print axioms C3T14_ok
#print axioms C3T14_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
