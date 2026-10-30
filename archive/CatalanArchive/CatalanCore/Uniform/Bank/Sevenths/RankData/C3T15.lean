import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 094f065a3568810fd048526329b97bef7229ab0e8f9688cef9574cfd47dc8b49, root class 3. -/
def C3T15 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 5) | 2 => (-29 / 60) | 3 => (-197 / 380) | 4 => (-664 / 1235) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24 / 25) | 2 => (-3781 / 3600) | 3 => (-465647 / 433200) | 4 => (-9928171 / 9151350) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-411709889794699 / 694156807447285) | 1, 1 => 1 | 1, 4 => (-12879997371908 / 59499154924053) | 2, 2 => 1 | 2, 4 => (-18175607642096 / 138831361489457) | 3, 3 => 1 | 3, 4 => (-684354583296 / 7306913762603) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (411709889794699 / 694156807447285) | 1, 1 => 1 | 1, 4 => (12879997371908 / 59499154924053) | 2, 2 => 1 | 2, 4 => (18175607642096 / 138831361489457) | 3, 3 => 1 | 3, 4 => (684354583296 / 7306913762603) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C3T15_ok : C3T15.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T15_den : ℕ := 2082470422341855
theorem C3T15_den_ok :
    (∀ d ∈ C3T15.R, ∀ e ∈ C3T15.R, (C3T15.Lq d e).den ∣ C3T15_den ∧ (C3T15.Lq' d e).den ∣ C3T15_den) ∧
    (∀ d ∈ C3T15.C, ∀ e ∈ C3T15.C, (C3T15.Pq d e).den ∣ C3T15_den ∧ (C3T15.Pq' d e).den ∣ C3T15_den) := by
  constructor <;> decide +kernel
theorem C3T15_cload_4 : C3T15.cload 4 = ((-71134325929822 / 2082470422341855), (-141287501650532 / 416494084468371)) := by decide +kernel
#print axioms C3T15_ok
#print axioms C3T15_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
