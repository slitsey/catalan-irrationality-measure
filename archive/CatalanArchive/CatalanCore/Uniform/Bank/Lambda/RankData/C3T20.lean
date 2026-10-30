import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type a659f23db98fea6735abd1858959d080b0a0659dba0f3f73b1991addbf5efe59, root class 3. -/
def C3T20 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 3) | 2 => (-17 / 42) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-7 / 9) | 2 => (-1507 / 1764) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-137 / 84) | 2, 1 => (-17 / 28) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (137 / 84) | 2, 1 => (17 / 28) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C3T20_ok : C3T20.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T20_den : ℕ := 84
theorem C3T20_den_ok :
    (∀ d ∈ C3T20.R, ∀ e ∈ C3T20.R, (C3T20.Lq d e).den ∣ C3T20_den ∧ (C3T20.Lq' d e).den ∣ C3T20_den) ∧
    (∀ d ∈ C3T20.C, ∀ e ∈ C3T20.C, (C3T20.Pq d e).den ∣ C3T20_den ∧ (C3T20.Pq' d e).den ∣ C3T20_den) := by
  constructor <;> decide +kernel
theorem C3T20_rload_2 : C3T20.rload 2 = ((-26 / 21), (-17 / 84)) := by decide +kernel
#print axioms C3T20_ok
#print axioms C3T20_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
