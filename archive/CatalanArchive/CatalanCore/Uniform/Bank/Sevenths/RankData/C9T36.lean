import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type bda2ea421c5b02c7878af3f5a6023b4599285c66d5e5ceeb6e5f73ff2beb747f, root class 9. -/
def C9T36 : FibreCert where
  R := {0}
  C := ∅
  lf := fun d => match d with | 0 => (-7 / 4) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun _ _ => 0
  Pq' := fun _ _ => 0
  kr := {0}
  kc := ∅

theorem C9T36_ok : C9T36.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T36_den : ℕ := 1
theorem C9T36_den_ok :
    (∀ d ∈ C9T36.R, ∀ e ∈ C9T36.R, (C9T36.Lq d e).den ∣ C9T36_den ∧ (C9T36.Lq' d e).den ∣ C9T36_den) ∧
    (∀ d ∈ C9T36.C, ∀ e ∈ C9T36.C, (C9T36.Pq d e).den ∣ C9T36_den ∧ (C9T36.Pq' d e).den ∣ C9T36_den) := by
  constructor <;> decide +kernel
theorem C9T36_rload_0 : C9T36.rload 0 = (1, (-7 / 4)) := by decide +kernel
#print axioms C9T36_ok
#print axioms C9T36_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
