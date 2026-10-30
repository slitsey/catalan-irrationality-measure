import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type febe4e1766cedad8dfa9065476d317f93e74011af11b6e04c6cca2f3cebc1402, root class 3. -/
def C3T07 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 3) | 2 => (-17 / 42) | 3 => (-67 / 154) | 4 => (-2087 / 4620) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-7 / 9) | 2 => (-1507 / 1764) | 3 => (-62285 / 71148) | 4 => (-18869299 / 21344400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T07_ok : C3T07.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T07_den : ℕ := 1
theorem C3T07_den_ok :
    (∀ d ∈ C3T07.R, ∀ e ∈ C3T07.R, (C3T07.Lq d e).den ∣ C3T07_den ∧ (C3T07.Lq' d e).den ∣ C3T07_den) ∧
    (∀ d ∈ C3T07.C, ∀ e ∈ C3T07.C, (C3T07.Pq d e).den ∣ C3T07_den ∧ (C3T07.Pq' d e).den ∣ C3T07_den) := by
  constructor <;> decide +kernel
#print axioms C3T07_ok
#print axioms C3T07_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
