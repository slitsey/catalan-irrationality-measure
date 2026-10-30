import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 53a1487e84beac07dea9dc1761955a9a0af72303c48c0196839a6f2063ceb2cc, root class 5. -/
def C5T31 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (-27 / 490) | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (27 / 490) | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C5T31_ok : C5T31.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T31_den : ℕ := 490
theorem C5T31_den_ok :
    (∀ d ∈ C5T31.R, ∀ e ∈ C5T31.R, (C5T31.Lq d e).den ∣ C5T31_den ∧ (C5T31.Lq' d e).den ∣ C5T31_den) ∧
    (∀ d ∈ C5T31.C, ∀ e ∈ C5T31.C, (C5T31.Pq d e).den ∣ C5T31_den ∧ (C5T31.Pq' d e).den ∣ C5T31_den) := by
  constructor <;> decide +kernel
theorem C5T31_rload_1 : C5T31.rload 1 = ((463 / 490), (-40 / 21)) := by decide +kernel
#print axioms C5T31_ok
#print axioms C5T31_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
