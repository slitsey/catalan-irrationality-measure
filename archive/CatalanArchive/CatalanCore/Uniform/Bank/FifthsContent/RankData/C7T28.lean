import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 76d0dff6eb6e9e5865f84890344c543f31cd765b9340cccb098a6407fd802514, prime class 7 mod 10. -/
def C7T28 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => (-5 / 3) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C7T28_ok : C7T28.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T28_den : ℕ := 1
theorem C7T28_den_ok :
    (∀ d ∈ C7T28.R, ∀ e ∈ C7T28.R, (C7T28.Lq d e).den ∣ C7T28_den ∧ (C7T28.Lq' d e).den ∣ C7T28_den) ∧
    (∀ d ∈ C7T28.C, ∀ e ∈ C7T28.C, (C7T28.Pq d e).den ∣ C7T28_den ∧ (C7T28.Pq' d e).den ∣ C7T28_den) := by
  constructor <;> decide +kernel
theorem C7T28_cload_0 : C7T28.cload 0 = (1, (-5 / 3)) := by decide +kernel
#print axioms C7T28_ok
#print axioms C7T28_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
