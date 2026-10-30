import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 51fea1c0b0112718f02d21a93994de881337317603dd6ce31c97ec05eee1b165, prime class 9 mod 10. -/
def C9T10 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | 2 => (-11 / 36) | 3 => (-83 / 252) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | 2 => (-805 / 1296) | 3 => (-40489 / 63504) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T10_ok : C9T10.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T10_den : ℕ := 1
theorem C9T10_den_ok :
    (∀ d ∈ C9T10.R, ∀ e ∈ C9T10.R, (C9T10.Lq d e).den ∣ C9T10_den ∧ (C9T10.Lq' d e).den ∣ C9T10_den) ∧
    (∀ d ∈ C9T10.C, ∀ e ∈ C9T10.C, (C9T10.Pq d e).den ∣ C9T10_den ∧ (C9T10.Pq' d e).den ∣ C9T10_den) := by
  constructor <;> decide +kernel
#print axioms C9T10_ok
#print axioms C9T10_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
