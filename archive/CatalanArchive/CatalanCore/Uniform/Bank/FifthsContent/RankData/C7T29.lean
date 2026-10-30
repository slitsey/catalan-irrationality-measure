import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 26a73cbcfeb5a1082f1b0831c5d0c2ccd62342ee5b7e78e9a784a2e5ee63bc8b, prime class 7 mod 10. -/
def C7T29 : FibreCert where
  R := {0}
  C := ∅
  lf := fun d => match d with | 0 => 0 | _ => 0
  ee := fun d => match d with | 0 => 0 | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun _ _ => 0
  Pq' := fun _ _ => 0
  kr := {0}
  kc := ∅

theorem C7T29_ok : C7T29.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T29_den : ℕ := 1
theorem C7T29_den_ok :
    (∀ d ∈ C7T29.R, ∀ e ∈ C7T29.R, (C7T29.Lq d e).den ∣ C7T29_den ∧ (C7T29.Lq' d e).den ∣ C7T29_den) ∧
    (∀ d ∈ C7T29.C, ∀ e ∈ C7T29.C, (C7T29.Pq d e).den ∣ C7T29_den ∧ (C7T29.Pq' d e).den ∣ C7T29_den) := by
  constructor <;> decide +kernel
theorem C7T29_rload_0 : C7T29.rload 0 = (1, 0) := by decide +kernel
#print axioms C7T29_ok
#print axioms C7T29_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
