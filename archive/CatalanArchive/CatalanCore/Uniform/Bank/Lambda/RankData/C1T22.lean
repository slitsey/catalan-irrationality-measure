import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 1d227d47ce34dea971629ea9256b2a7dba317aaf02386ce7b04d3ded99eb2c1b, root class 1. -/
def C1T22 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-3) | 2 => (-33 / 10) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-15) | 2 => (-1539 / 100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-57 / 20) | 1, 1 => 1 | 1, 2 => (-11 / 20) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (57 / 20) | 1, 1 => 1 | 1, 2 => (11 / 20) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C1T22_ok : C1T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T22_den : ℕ := 20
theorem C1T22_den_ok :
    (∀ d ∈ C1T22.R, ∀ e ∈ C1T22.R, (C1T22.Lq d e).den ∣ C1T22_den ∧ (C1T22.Lq' d e).den ∣ C1T22_den) ∧
    (∀ d ∈ C1T22.C, ∀ e ∈ C1T22.C, (C1T22.Pq d e).den ∣ C1T22_den ∧ (C1T22.Pq' d e).den ∣ C1T22_den) := by
  constructor <;> decide +kernel
theorem C1T22_cload_2 : C1T22.cload 2 = ((-12 / 5), (-33 / 20)) := by decide +kernel
#print axioms C1T22_ok
#print axioms C1T22_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
