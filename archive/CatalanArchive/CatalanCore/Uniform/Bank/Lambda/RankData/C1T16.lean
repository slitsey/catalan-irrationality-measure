import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 2dd4af91aa90ce8107ba6c3ea9c3088fe8e84f74b468186fddcabba6c3d5ff06, root class 1. -/
def C1T16 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-3) | 2 => (-33 / 10) | 3 => (-307 / 90) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-15) | 2 => (-1539 / 100) | 3 => (-125359 / 8100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-3297899 / 2187810) | 3, 1 => (-254641 / 875124) | 3, 2 => (-1297 / 8103) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (3297899 / 2187810) | 3, 1 => (254641 / 875124) | 3, 2 => (1297 / 8103) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C1T16_ok : C1T16.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T16_den : ℕ := 4375620
theorem C1T16_den_ok :
    (∀ d ∈ C1T16.R, ∀ e ∈ C1T16.R, (C1T16.Lq d e).den ∣ C1T16_den ∧ (C1T16.Lq' d e).den ∣ C1T16_den) ∧
    (∀ d ∈ C1T16.C, ∀ e ∈ C1T16.C, (C1T16.Pq d e).den ∣ C1T16_den ∧ (C1T16.Pq' d e).den ∣ C1T16_den) := by
  constructor <;> decide +kernel
theorem C1T16_rload_3 : C1T16.rload 3 = ((-1397921 / 1458540), (-2931619 / 1458540)) := by decide +kernel
#print axioms C1T16_ok
#print axioms C1T16_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
