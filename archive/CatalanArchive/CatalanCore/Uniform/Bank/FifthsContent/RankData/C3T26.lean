import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 54422fa50b67c9bd1fb9ffbbf05a94c75952b82eb6a11059a6721d50857c8ee6, prime class 3 mod 10. -/
def C3T26 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => (-5 / 2) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T26_ok : C3T26.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T26_den : ℕ := 1
theorem C3T26_den_ok :
    (∀ d ∈ C3T26.R, ∀ e ∈ C3T26.R, (C3T26.Lq d e).den ∣ C3T26_den ∧ (C3T26.Lq' d e).den ∣ C3T26_den) ∧
    (∀ d ∈ C3T26.C, ∀ e ∈ C3T26.C, (C3T26.Pq d e).den ∣ C3T26_den ∧ (C3T26.Pq' d e).den ∣ C3T26_den) := by
  constructor <;> decide +kernel
#print axioms C3T26_ok
#print axioms C3T26_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
