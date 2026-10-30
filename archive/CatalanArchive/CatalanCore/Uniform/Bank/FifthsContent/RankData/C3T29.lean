import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 7129cc5a0daebea1a03b8d17ecefb9d56907b4c423020899f4318c89a7c37183, prime class 3 mod 10. -/
def C3T29 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => 0 | _ => 0
  ee := fun d => match d with | 0 => 0 | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {0}
  kc := {0}

theorem C3T29_ok : C3T29.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T29_den : ℕ := 1
theorem C3T29_den_ok :
    (∀ d ∈ C3T29.R, ∀ e ∈ C3T29.R, (C3T29.Lq d e).den ∣ C3T29_den ∧ (C3T29.Lq' d e).den ∣ C3T29_den) ∧
    (∀ d ∈ C3T29.C, ∀ e ∈ C3T29.C, (C3T29.Pq d e).den ∣ C3T29_den ∧ (C3T29.Pq' d e).den ∣ C3T29_den) := by
  constructor <;> decide +kernel
theorem C3T29_rload_0 : C3T29.rload 0 = (1, 0) := by decide +kernel
theorem C3T29_cload_0 : C3T29.cload 0 = (1, 0) := by decide +kernel
#print axioms C3T29_ok
#print axioms C3T29_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
