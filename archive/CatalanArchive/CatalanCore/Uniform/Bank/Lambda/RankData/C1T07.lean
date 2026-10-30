import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type cae9192b391ae70c7d3253e70a9f3fb146abf752fb68987a02d987df8716b85b, root class 1. -/
def C1T07 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-3) | 2 => (-33 / 10) | 3 => (-307 / 90) | 4 => (-8117 / 2340) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-15) | 2 => (-1539 / 100) | 3 => (-125359 / 8100) | 4 => (-84918859 / 5475600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T07_ok : C1T07.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T07_den : ℕ := 1
theorem C1T07_den_ok :
    (∀ d ∈ C1T07.R, ∀ e ∈ C1T07.R, (C1T07.Lq d e).den ∣ C1T07_den ∧ (C1T07.Lq' d e).den ∣ C1T07_den) ∧
    (∀ d ∈ C1T07.C, ∀ e ∈ C1T07.C, (C1T07.Pq d e).den ∣ C1T07_den ∧ (C1T07.Pq' d e).den ∣ C1T07_den) := by
  constructor <;> decide +kernel
#print axioms C1T07_ok
#print axioms C1T07_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
