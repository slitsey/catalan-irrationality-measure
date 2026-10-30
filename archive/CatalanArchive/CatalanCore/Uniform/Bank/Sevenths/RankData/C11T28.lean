import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c90b854cd3a206bf90e9b772a5f920d7fa81993094f04f18f8a0ad8a26c852aa, root class 11. -/
def C11T28 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | 2 => (-25 / 9) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | 2 => (-940 / 81) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-47 / 18) | 1, 1 => 1 | 1, 2 => (-5 / 9) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (47 / 18) | 1, 1 => 1 | 1, 2 => (5 / 9) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C11T28_ok : C11T28.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T28_den : ℕ := 18
theorem C11T28_den_ok :
    (∀ d ∈ C11T28.R, ∀ e ∈ C11T28.R, (C11T28.Lq d e).den ∣ C11T28_den ∧ (C11T28.Lq' d e).den ∣ C11T28_den) ∧
    (∀ d ∈ C11T28.C, ∀ e ∈ C11T28.C, (C11T28.Pq d e).den ∣ C11T28_den ∧ (C11T28.Pq' d e).den ∣ C11T28_den) := by
  constructor <;> decide +kernel
theorem C11T28_cload_2 : C11T28.cload 2 = ((-13 / 6), (-25 / 18)) := by decide +kernel
#print axioms C11T28_ok
#print axioms C11T28_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
