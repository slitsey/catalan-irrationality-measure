import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d8eaf4f764d4d590af4faa46a1f75ca4c2d55458b2202a5c2fb449871ec6deec, root class 3. -/
def C3T20 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 5) | 2 => (-29 / 60) | 3 => (-197 / 380) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24 / 25) | 2 => (-3781 / 3600) | 3 => (-465647 / 433200) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-85532647 / 98587200) | 1, 1 => 1 | 1, 3 => (-4159379 / 13144960) | 2, 2 => 1 | 2, 3 => (-8273 / 43240) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (85532647 / 98587200) | 1, 1 => 1 | 1, 3 => (4159379 / 13144960) | 2, 2 => 1 | 2, 3 => (8273 / 43240) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C3T20_ok : C3T20.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T20_den : ℕ := 197174400
theorem C3T20_den_ok :
    (∀ d ∈ C3T20.R, ∀ e ∈ C3T20.R, (C3T20.Lq d e).den ∣ C3T20_den ∧ (C3T20.Lq' d e).den ∣ C3T20_den) ∧
    (∀ d ∈ C3T20.C, ∀ e ∈ C3T20.C, (C3T20.Pq d e).den ∣ C3T20_den ∧ (C3T20.Pq' d e).den ∣ C3T20_den) := by
  constructor <;> decide +kernel
theorem C3T20_cload_3 : C3T20.cload 3 = ((-74006459 / 197174400), (-29514697 / 98587200)) := by decide +kernel
#print axioms C3T20_ok
#print axioms C3T20_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
