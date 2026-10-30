import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 78e53980e43defe7957589b879d9b1a6fbb4fb9b2f159e266f575db0d59003aa, root class 11. -/
def C11T36 : FibreCert where
  R := {0}
  C := ∅
  lf := fun d => match d with | 0 => (-7 / 2) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun _ _ => 0
  Pq' := fun _ _ => 0
  kr := {0}
  kc := ∅

theorem C11T36_ok : C11T36.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T36_den : ℕ := 1
theorem C11T36_den_ok :
    (∀ d ∈ C11T36.R, ∀ e ∈ C11T36.R, (C11T36.Lq d e).den ∣ C11T36_den ∧ (C11T36.Lq' d e).den ∣ C11T36_den) ∧
    (∀ d ∈ C11T36.C, ∀ e ∈ C11T36.C, (C11T36.Pq d e).den ∣ C11T36_den ∧ (C11T36.Pq' d e).den ∣ C11T36_den) := by
  constructor <;> decide +kernel
theorem C11T36_rload_0 : C11T36.rload 0 = (1, (-7 / 2)) := by decide +kernel
#print axioms C11T36_ok
#print axioms C11T36_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
