import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 30809515a37942aa7c2fe155708dce2af8ef8be1332710f07fd8f8256a1d4f0b, root class 5. -/
def C5T33 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C5T33_ok : C5T33.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T33_den : ℕ := 1
theorem C5T33_den_ok :
    (∀ d ∈ C5T33.R, ∀ e ∈ C5T33.R, (C5T33.Lq d e).den ∣ C5T33_den ∧ (C5T33.Lq' d e).den ∣ C5T33_den) ∧
    (∀ d ∈ C5T33.C, ∀ e ∈ C5T33.C, (C5T33.Pq d e).den ∣ C5T33_den ∧ (C5T33.Pq' d e).den ∣ C5T33_den) := by
  constructor <;> decide +kernel
theorem C5T33_cload_1 : C5T33.cload 1 = (1, 0) := by decide +kernel
#print axioms C5T33_ok
#print axioms C5T33_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
