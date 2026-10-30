import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 7129cc5a0daebea1a03b8d17ecefb9d56907b4c423020899f4318c89a7c37183, prime class 9 mod 10. -/
def C9T26 : FibreCert where
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

theorem C9T26_ok : C9T26.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T26_den : ℕ := 1
theorem C9T26_den_ok :
    (∀ d ∈ C9T26.R, ∀ e ∈ C9T26.R, (C9T26.Lq d e).den ∣ C9T26_den ∧ (C9T26.Lq' d e).den ∣ C9T26_den) ∧
    (∀ d ∈ C9T26.C, ∀ e ∈ C9T26.C, (C9T26.Pq d e).den ∣ C9T26_den ∧ (C9T26.Pq' d e).den ∣ C9T26_den) := by
  constructor <;> decide +kernel
theorem C9T26_rload_0 : C9T26.rload 0 = (1, 0) := by decide +kernel
theorem C9T26_cload_0 : C9T26.cload 0 = (1, 0) := by decide +kernel
#print axioms C9T26_ok
#print axioms C9T26_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
