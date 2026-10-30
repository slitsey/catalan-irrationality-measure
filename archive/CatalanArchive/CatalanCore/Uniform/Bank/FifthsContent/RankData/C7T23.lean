import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 95965a02f729f28da4c2f30df6cb323eb9f0276e2422ba52f0776a536b68f244, prime class 7 mod 10. -/
def C7T23 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => (-5 / 3) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C7T23_ok : C7T23.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T23_den : ℕ := 1
theorem C7T23_den_ok :
    (∀ d ∈ C7T23.R, ∀ e ∈ C7T23.R, (C7T23.Lq d e).den ∣ C7T23_den ∧ (C7T23.Lq' d e).den ∣ C7T23_den) ∧
    (∀ d ∈ C7T23.C, ∀ e ∈ C7T23.C, (C7T23.Pq d e).den ∣ C7T23_den ∧ (C7T23.Pq' d e).den ∣ C7T23_den) := by
  constructor <;> decide +kernel
#print axioms C7T23_ok
#print axioms C7T23_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
