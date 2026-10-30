import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 461bb09da466ec163da6f1085a6bd69951cd10e6e8ae5b0a59f47507db8041a7, prime class 9 mod 10. -/
def C9T22 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => (-5 / 4) | 1 => (-29 / 36) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | 1 => (-1129 / 1296) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (-64 / 225) | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (64 / 225) | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C9T22_ok : C9T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T22_den : ℕ := 225
theorem C9T22_den_ok :
    (∀ d ∈ C9T22.R, ∀ e ∈ C9T22.R, (C9T22.Lq d e).den ∣ C9T22_den ∧ (C9T22.Lq' d e).den ∣ C9T22_den) ∧
    (∀ d ∈ C9T22.C, ∀ e ∈ C9T22.C, (C9T22.Pq d e).den ∣ C9T22_den ∧ (C9T22.Pq' d e).den ∣ C9T22_den) := by
  constructor <;> decide +kernel
theorem C9T22_rload_1 : C9T22.rload 1 = ((161 / 225), (-9 / 20)) := by decide +kernel
#print axioms C9T22_ok
#print axioms C9T22_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
