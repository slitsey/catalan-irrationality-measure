import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 8ada38bbf2405637a0fe5ff8b30860fba5ad039d16cdbf15a45fd44b7d18db40, root class 13. -/
def C13T32 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C13T32_ok : C13T32.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T32_den : ℕ := 1
theorem C13T32_den_ok :
    (∀ d ∈ C13T32.R, ∀ e ∈ C13T32.R, (C13T32.Lq d e).den ∣ C13T32_den ∧ (C13T32.Lq' d e).den ∣ C13T32_den) ∧
    (∀ d ∈ C13T32.C, ∀ e ∈ C13T32.C, (C13T32.Pq d e).den ∣ C13T32_den ∧ (C13T32.Pq' d e).den ∣ C13T32_den) := by
  constructor <;> decide +kernel
theorem C13T32_cload_1 : C13T32.cload 1 = (1, 0) := by decide +kernel
#print axioms C13T32_ok
#print axioms C13T32_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
