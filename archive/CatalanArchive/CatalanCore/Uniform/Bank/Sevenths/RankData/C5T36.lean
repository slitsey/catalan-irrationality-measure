import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type fb56bc13b424b41d0146da082d7550b81af7d90c3e1fb8f387e2c6c827b381cc, root class 5. -/
def C5T36 : FibreCert where
  R := {0}
  C := ∅
  lf := fun d => match d with | 0 => (-7 / 3) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun _ _ => 0
  Pq' := fun _ _ => 0
  kr := {0}
  kc := ∅

theorem C5T36_ok : C5T36.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T36_den : ℕ := 1
theorem C5T36_den_ok :
    (∀ d ∈ C5T36.R, ∀ e ∈ C5T36.R, (C5T36.Lq d e).den ∣ C5T36_den ∧ (C5T36.Lq' d e).den ∣ C5T36_den) ∧
    (∀ d ∈ C5T36.C, ∀ e ∈ C5T36.C, (C5T36.Pq d e).den ∣ C5T36_den ∧ (C5T36.Pq' d e).den ∣ C5T36_den) := by
  constructor <;> decide +kernel
theorem C5T36_rload_0 : C5T36.rload 0 = (1, (-7 / 3)) := by decide +kernel
#print axioms C5T36_ok
#print axioms C5T36_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
