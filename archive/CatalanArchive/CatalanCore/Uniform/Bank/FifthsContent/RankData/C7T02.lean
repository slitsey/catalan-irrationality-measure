import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type b8a59561a6ba60157308de0b4f4feb990e45ab81a5638ff690727292f2c88e1a, prime class 7 mod 10. -/
def C7T02 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | 2 => (-19 / 24) | 3 => (-263 / 312) | 4 => (-815 / 936) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | 2 => (-1105 / 576) | 3 => (-63443 / 32448) | 4 => (-1725805 / 876096) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C7T02_ok : C7T02.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T02_den : ℕ := 1
theorem C7T02_den_ok :
    (∀ d ∈ C7T02.R, ∀ e ∈ C7T02.R, (C7T02.Lq d e).den ∣ C7T02_den ∧ (C7T02.Lq' d e).den ∣ C7T02_den) ∧
    (∀ d ∈ C7T02.C, ∀ e ∈ C7T02.C, (C7T02.Pq d e).den ∣ C7T02_den ∧ (C7T02.Pq' d e).den ∣ C7T02_den) := by
  constructor <;> decide +kernel
#print axioms C7T02_ok
#print axioms C7T02_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
