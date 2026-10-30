import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 4bdd08a315bf4d2f5cbcde19892b33a79b0f5690dcbb997c6a8583304b8a7d44, prime class 7 mod 10. -/
def C7T20 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C7T20_ok : C7T20.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T20_den : ℕ := 1
theorem C7T20_den_ok :
    (∀ d ∈ C7T20.R, ∀ e ∈ C7T20.R, (C7T20.Lq d e).den ∣ C7T20_den ∧ (C7T20.Lq' d e).den ∣ C7T20_den) ∧
    (∀ d ∈ C7T20.C, ∀ e ∈ C7T20.C, (C7T20.Pq d e).den ∣ C7T20_den ∧ (C7T20.Pq' d e).den ∣ C7T20_den) := by
  constructor <;> decide +kernel
#print axioms C7T20_ok
#print axioms C7T20_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
