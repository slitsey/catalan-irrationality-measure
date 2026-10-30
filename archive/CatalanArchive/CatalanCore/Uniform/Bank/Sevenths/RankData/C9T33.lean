import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c45b3727c950165a26209f926ffe27941ff05b701b1d5f65cf233259ab4462ba, root class 9. -/
def C9T33 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C9T33_ok : C9T33.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T33_den : ℕ := 1
theorem C9T33_den_ok :
    (∀ d ∈ C9T33.R, ∀ e ∈ C9T33.R, (C9T33.Lq d e).den ∣ C9T33_den ∧ (C9T33.Lq' d e).den ∣ C9T33_den) ∧
    (∀ d ∈ C9T33.C, ∀ e ∈ C9T33.C, (C9T33.Pq d e).den ∣ C9T33_den ∧ (C9T33.Pq' d e).den ∣ C9T33_den) := by
  constructor <;> decide +kernel
theorem C9T33_cload_1 : C9T33.cload 1 = (1, 0) := by decide +kernel
#print axioms C9T33_ok
#print axioms C9T33_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
