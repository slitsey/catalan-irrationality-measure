import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 1d3e4a3a5347fd10bf586b27b06a2db2cd5709481f02a326b78216734dceea9e, prime class 3 mod 10. -/
def C3T28 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | _ => 0
  Lq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C3T28_ok : C3T28.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T28_den : ℕ := 1
theorem C3T28_den_ok :
    (∀ d ∈ C3T28.R, ∀ e ∈ C3T28.R, (C3T28.Lq d e).den ∣ C3T28_den ∧ (C3T28.Lq' d e).den ∣ C3T28_den) ∧
    (∀ d ∈ C3T28.C, ∀ e ∈ C3T28.C, (C3T28.Pq d e).den ∣ C3T28_den ∧ (C3T28.Pq' d e).den ∣ C3T28_den) := by
  constructor <;> decide +kernel
theorem C3T28_rload_1 : C3T28.rload 1 = (1, 0) := by decide +kernel
#print axioms C3T28_ok
#print axioms C3T28_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
