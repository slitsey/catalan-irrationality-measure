import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type cefc6d30ac72828a6a762e5cf6ca01fcceb0203fb66c43966f705aa069e4345d, prime class 1 mod 10. -/
def C1T04 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-5) | 1 => (-29 / 6) | 2 => (-158 / 33) | 3 => (-839 / 176) | 4 => (-17575 / 3696) | _ => 0
  ee := fun d => match d with | 0 => (-25) | 1 => (-889 / 36) | 2 => (-26845 / 1089) | 3 => (-2289523 / 92928) | 4 => (-336480505 / 13660416) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T04_ok : C1T04.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T04_den : ℕ := 1
theorem C1T04_den_ok :
    (∀ d ∈ C1T04.R, ∀ e ∈ C1T04.R, (C1T04.Lq d e).den ∣ C1T04_den ∧ (C1T04.Lq' d e).den ∣ C1T04_den) ∧
    (∀ d ∈ C1T04.C, ∀ e ∈ C1T04.C, (C1T04.Pq d e).den ∣ C1T04_den ∧ (C1T04.Pq' d e).den ∣ C1T04_den) := by
  constructor <;> decide +kernel
#print axioms C1T04_ok
#print axioms C1T04_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
