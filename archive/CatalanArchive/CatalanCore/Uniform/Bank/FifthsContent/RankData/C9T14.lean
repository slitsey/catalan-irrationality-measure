import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 47cbb14da045db4fb610dfa93118585b1d2c8ac74488ada12a8882c0e72780e1, prime class 9 mod 10. -/
def C9T14 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | 2 => (-11 / 36) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | 2 => (-805 / 1296) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T14_ok : C9T14.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T14_den : ℕ := 1
theorem C9T14_den_ok :
    (∀ d ∈ C9T14.R, ∀ e ∈ C9T14.R, (C9T14.Lq d e).den ∣ C9T14_den ∧ (C9T14.Lq' d e).den ∣ C9T14_den) ∧
    (∀ d ∈ C9T14.C, ∀ e ∈ C9T14.C, (C9T14.Pq d e).den ∣ C9T14_den ∧ (C9T14.Pq' d e).den ∣ C9T14_den) := by
  constructor <;> decide +kernel
#print axioms C9T14_ok
#print axioms C9T14_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
