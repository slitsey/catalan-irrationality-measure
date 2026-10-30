import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 0d02bf9b50de8772efc3be7105d0d2567559569d8a59604747bf562ea97b4194, root class 1. -/
def C1T32 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => (-7) | _ => 0
  ee := fun d => match d with | 0 => (-49) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T32_ok : C1T32.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T32_den : ℕ := 1
theorem C1T32_den_ok :
    (∀ d ∈ C1T32.R, ∀ e ∈ C1T32.R, (C1T32.Lq d e).den ∣ C1T32_den ∧ (C1T32.Lq' d e).den ∣ C1T32_den) ∧
    (∀ d ∈ C1T32.C, ∀ e ∈ C1T32.C, (C1T32.Pq d e).den ∣ C1T32_den ∧ (C1T32.Pq' d e).den ∣ C1T32_den) := by
  constructor <;> decide +kernel
#print axioms C1T32_ok
#print axioms C1T32_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
