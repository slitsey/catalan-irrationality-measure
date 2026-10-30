import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 111dda1df85ab8734a581c1bd9906a8925ca7a9d00845b71d948755f9f64ade4, prime class 7 mod 10. -/
def C7T16 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | 2 => (-19 / 24) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | 2 => (-1105 / 576) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C7T16_ok : C7T16.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T16_den : ℕ := 1
theorem C7T16_den_ok :
    (∀ d ∈ C7T16.R, ∀ e ∈ C7T16.R, (C7T16.Lq d e).den ∣ C7T16_den ∧ (C7T16.Lq' d e).den ∣ C7T16_den) ∧
    (∀ d ∈ C7T16.C, ∀ e ∈ C7T16.C, (C7T16.Pq d e).den ∣ C7T16_den ∧ (C7T16.Pq' d e).den ∣ C7T16_den) := by
  constructor <;> decide +kernel
#print axioms C7T16_ok
#print axioms C7T16_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
