import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 16b6a48c3b387d18a2368a52e4d36381ccfe104eefa91803f760bdf3bcb7d562, root class 1. -/
def C1T35 : FibreCert where
  R := {0}
  C := ∅
  lf := fun d => match d with | 0 => (-7) | _ => 0
  ee := fun d => match d with | 0 => (-49) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun _ _ => 0
  Pq' := fun _ _ => 0
  kr := {0}
  kc := ∅

theorem C1T35_ok : C1T35.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T35_den : ℕ := 1
theorem C1T35_den_ok :
    (∀ d ∈ C1T35.R, ∀ e ∈ C1T35.R, (C1T35.Lq d e).den ∣ C1T35_den ∧ (C1T35.Lq' d e).den ∣ C1T35_den) ∧
    (∀ d ∈ C1T35.C, ∀ e ∈ C1T35.C, (C1T35.Pq d e).den ∣ C1T35_den ∧ (C1T35.Pq' d e).den ∣ C1T35_den) := by
  constructor <;> decide +kernel
theorem C1T35_rload_0 : C1T35.rload 0 = (1, (-7)) := by decide +kernel
#print axioms C1T35_ok
#print axioms C1T35_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
