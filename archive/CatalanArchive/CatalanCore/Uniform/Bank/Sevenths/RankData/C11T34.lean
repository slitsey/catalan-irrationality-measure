import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 5091103bd4b6b11f9e59a295c98c7a15517795a45e57265550f61cef065de81d, root class 11. -/
def C11T34 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | _ => 0
  Lq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C11T34_ok : C11T34.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T34_den : ℕ := 1
theorem C11T34_den_ok :
    (∀ d ∈ C11T34.R, ∀ e ∈ C11T34.R, (C11T34.Lq d e).den ∣ C11T34_den ∧ (C11T34.Lq' d e).den ∣ C11T34_den) ∧
    (∀ d ∈ C11T34.C, ∀ e ∈ C11T34.C, (C11T34.Pq d e).den ∣ C11T34_den ∧ (C11T34.Pq' d e).den ∣ C11T34_den) := by
  constructor <;> decide +kernel
theorem C11T34_rload_1 : C11T34.rload 1 = (1, 0) := by decide +kernel
#print axioms C11T34_ok
#print axioms C11T34_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
