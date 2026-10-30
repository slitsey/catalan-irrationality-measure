import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 26a73cbcfeb5a1082f1b0831c5d0c2ccd62342ee5b7e78e9a784a2e5ee63bc8b, prime class 9 mod 10. -/
def C9T29 : FibreCert where
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

theorem C9T29_ok : C9T29.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T29_den : ℕ := 1
theorem C9T29_den_ok :
    (∀ d ∈ C9T29.R, ∀ e ∈ C9T29.R, (C9T29.Lq d e).den ∣ C9T29_den ∧ (C9T29.Lq' d e).den ∣ C9T29_den) ∧
    (∀ d ∈ C9T29.C, ∀ e ∈ C9T29.C, (C9T29.Pq d e).den ∣ C9T29_den ∧ (C9T29.Pq' d e).den ∣ C9T29_den) := by
  constructor <;> decide +kernel
theorem C9T29_rload_0 : C9T29.rload 0 = (1, 0) := by decide +kernel
#print axioms C9T29_ok
#print axioms C9T29_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
