import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type da78c0be6d76cbfe28f625ce07f6c4b684d53ff588d04cf72a7ef056aa1e19a2, prime class 9 mod 10. -/
def C9T02 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | 2 => (-11 / 36) | 3 => (-83 / 252) | 4 => (-410 / 1197) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | 2 => (-805 / 1296) | 3 => (-40489 / 63504) | 4 => (-1846415 / 2865618) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T02_ok : C9T02.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T02_den : ℕ := 1
theorem C9T02_den_ok :
    (∀ d ∈ C9T02.R, ∀ e ∈ C9T02.R, (C9T02.Lq d e).den ∣ C9T02_den ∧ (C9T02.Lq' d e).den ∣ C9T02_den) ∧
    (∀ d ∈ C9T02.C, ∀ e ∈ C9T02.C, (C9T02.Pq d e).den ∣ C9T02_den ∧ (C9T02.Pq' d e).den ∣ C9T02_den) := by
  constructor <;> decide +kernel
#print axioms C9T02_ok
#print axioms C9T02_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
