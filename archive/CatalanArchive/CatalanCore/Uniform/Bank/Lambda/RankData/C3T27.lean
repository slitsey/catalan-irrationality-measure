import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 25d9f4e6b89fc879eecfd3fe9325e53f9f4cbc28e940d096ef5bdc74d3b436fd, root class 3. -/
def C3T27 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-7 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C3T27_ok : C3T27.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T27_den : ℕ := 1
theorem C3T27_den_ok :
    (∀ d ∈ C3T27.R, ∀ e ∈ C3T27.R, (C3T27.Lq d e).den ∣ C3T27_den ∧ (C3T27.Lq' d e).den ∣ C3T27_den) ∧
    (∀ d ∈ C3T27.C, ∀ e ∈ C3T27.C, (C3T27.Pq d e).den ∣ C3T27_den ∧ (C3T27.Pq' d e).den ∣ C3T27_den) := by
  constructor <;> decide +kernel
theorem C3T27_rload_1 : C3T27.rload 1 = (1, 0) := by decide +kernel
#print axioms C3T27_ok
#print axioms C3T27_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
