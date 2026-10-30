import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type cca0159df1b67165bcd67e7c076a6df8fa6c1b8b72e4619d059ccd5318eed454, root class 1. -/
def C1T36 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => (-7) | _ => 0
  ee := fun d => match d with | 0 => (-49) | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C1T36_ok : C1T36.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T36_den : ℕ := 1
theorem C1T36_den_ok :
    (∀ d ∈ C1T36.R, ∀ e ∈ C1T36.R, (C1T36.Lq d e).den ∣ C1T36_den ∧ (C1T36.Lq' d e).den ∣ C1T36_den) ∧
    (∀ d ∈ C1T36.C, ∀ e ∈ C1T36.C, (C1T36.Pq d e).den ∣ C1T36_den ∧ (C1T36.Pq' d e).den ∣ C1T36_den) := by
  constructor <;> decide +kernel
theorem C1T36_cload_0 : C1T36.cload 0 = (1, (-7)) := by decide +kernel
#print axioms C1T36_ok
#print axioms C1T36_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
