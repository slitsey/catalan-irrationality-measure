import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 903757e203824dfcaefa16c37cf955b93c8ecaec8cf332c824912625401dc1f1, root class 1. -/
def C1T15 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-3) | 2 => (-33 / 10) | 3 => (-307 / 90) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-15) | 2 => (-1539 / 100) | 3 => (-125359 / 8100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-3297899 / 2187810) | 1, 1 => 1 | 1, 3 => (-254641 / 875124) | 2, 2 => 1 | 2, 3 => (-1297 / 8103) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (3297899 / 2187810) | 1, 1 => 1 | 1, 3 => (254641 / 875124) | 2, 2 => 1 | 2, 3 => (1297 / 8103) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C1T15_ok : C1T15.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T15_den : ℕ := 4375620
theorem C1T15_den_ok :
    (∀ d ∈ C1T15.R, ∀ e ∈ C1T15.R, (C1T15.Lq d e).den ∣ C1T15_den ∧ (C1T15.Lq' d e).den ∣ C1T15_den) ∧
    (∀ d ∈ C1T15.C, ∀ e ∈ C1T15.C, (C1T15.Pq d e).den ∣ C1T15_den ∧ (C1T15.Pq' d e).den ∣ C1T15_den) := by
  constructor <;> decide +kernel
theorem C1T15_cload_3 : C1T15.cload 3 = ((-1397921 / 1458540), (-2931619 / 1458540)) := by decide +kernel
#print axioms C1T15_ok
#print axioms C1T15_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
