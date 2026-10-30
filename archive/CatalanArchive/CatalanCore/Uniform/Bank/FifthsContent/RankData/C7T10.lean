import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 77829bf39dbf08b36c614f4384aefb8bad83ac9e8af290aa307fc5597dc7397f, prime class 7 mod 10. -/
def C7T10 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | 2 => (-19 / 24) | 3 => (-263 / 312) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | 2 => (-1105 / 576) | 3 => (-63443 / 32448) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C7T10_ok : C7T10.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T10_den : ℕ := 1
theorem C7T10_den_ok :
    (∀ d ∈ C7T10.R, ∀ e ∈ C7T10.R, (C7T10.Lq d e).den ∣ C7T10_den ∧ (C7T10.Lq' d e).den ∣ C7T10_den) ∧
    (∀ d ∈ C7T10.C, ∀ e ∈ C7T10.C, (C7T10.Pq d e).den ∣ C7T10_den ∧ (C7T10.Pq' d e).den ∣ C7T10_den) := by
  constructor <;> decide +kernel
#print axioms C7T10_ok
#print axioms C7T10_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
