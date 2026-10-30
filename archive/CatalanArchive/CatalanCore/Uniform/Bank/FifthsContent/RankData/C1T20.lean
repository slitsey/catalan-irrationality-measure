import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 312187a39f7cdf2dfa902bcc1730f35d221eb138f99ff7c54d94b9bff1d3a90f, prime class 1 mod 10. -/
def C1T20 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-5) | 1 => (-29 / 6) | _ => 0
  ee := fun d => match d with | 0 => (-25) | 1 => (-889 / 36) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T20_ok : C1T20.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T20_den : ℕ := 1
theorem C1T20_den_ok :
    (∀ d ∈ C1T20.R, ∀ e ∈ C1T20.R, (C1T20.Lq d e).den ∣ C1T20_den ∧ (C1T20.Lq' d e).den ∣ C1T20_den) ∧
    (∀ d ∈ C1T20.C, ∀ e ∈ C1T20.C, (C1T20.Pq d e).den ∣ C1T20_den ∧ (C1T20.Pq' d e).den ∣ C1T20_den) := by
  constructor <;> decide +kernel
#print axioms C1T20_ok
#print axioms C1T20_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
