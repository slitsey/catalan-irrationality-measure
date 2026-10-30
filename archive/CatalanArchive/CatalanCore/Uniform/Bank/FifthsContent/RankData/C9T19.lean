import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 8c1d4d0e18ba1cf17833025d9d6cbda2ec8a6f463262bdb8992aec02af03ba3b, prime class 9 mod 10. -/
def C9T19 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-5 / 4) | 1 => (-29 / 36) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | 1 => (-1129 / 1296) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T19_ok : C9T19.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T19_den : ℕ := 1
theorem C9T19_den_ok :
    (∀ d ∈ C9T19.R, ∀ e ∈ C9T19.R, (C9T19.Lq d e).den ∣ C9T19_den ∧ (C9T19.Lq' d e).den ∣ C9T19_den) ∧
    (∀ d ∈ C9T19.C, ∀ e ∈ C9T19.C, (C9T19.Pq d e).den ∣ C9T19_den ∧ (C9T19.Pq' d e).den ∣ C9T19_den) := by
  constructor <;> decide +kernel
#print axioms C9T19_ok
#print axioms C9T19_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
