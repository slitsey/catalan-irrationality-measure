import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 5f95e0a7afefda3180674e24b4e371593f5a34757fb6569a828122418d543a17, prime class 1 mod 10. -/
def C1T14 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5) | 1 => (-29 / 6) | 2 => (-158 / 33) | _ => 0
  ee := fun d => match d with | 0 => (-25) | 1 => (-889 / 36) | 2 => (-26845 / 1089) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T14_ok : C1T14.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T14_den : ℕ := 1
theorem C1T14_den_ok :
    (∀ d ∈ C1T14.R, ∀ e ∈ C1T14.R, (C1T14.Lq d e).den ∣ C1T14_den ∧ (C1T14.Lq' d e).den ∣ C1T14_den) ∧
    (∀ d ∈ C1T14.C, ∀ e ∈ C1T14.C, (C1T14.Pq d e).den ∣ C1T14_den ∧ (C1T14.Pq' d e).den ∣ C1T14_den) := by
  constructor <;> decide +kernel
#print axioms C1T14_ok
#print axioms C1T14_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
