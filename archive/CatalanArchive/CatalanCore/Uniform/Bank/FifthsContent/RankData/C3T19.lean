import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 496ef0f9a64c0c366c59a347953f0e333d697a205048fd3c66bfb29e3d5e16bd, prime class 3 mod 10. -/
def C3T19 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | 2 => (-12 / 7) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | 2 => (-270 / 49) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T19_ok : C3T19.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T19_den : ℕ := 1
theorem C3T19_den_ok :
    (∀ d ∈ C3T19.R, ∀ e ∈ C3T19.R, (C3T19.Lq d e).den ∣ C3T19_den ∧ (C3T19.Lq' d e).den ∣ C3T19_den) ∧
    (∀ d ∈ C3T19.C, ∀ e ∈ C3T19.C, (C3T19.Pq d e).den ∣ C3T19_den ∧ (C3T19.Pq' d e).den ∣ C3T19_den) := by
  constructor <;> decide +kernel
#print axioms C3T19_ok
#print axioms C3T19_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
