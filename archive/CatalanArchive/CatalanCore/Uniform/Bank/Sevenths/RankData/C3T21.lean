import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 5413ba4fc5d23e8f4098a70449664e23bdb0b05e86dd2d499ee35ed59fd08e80, root class 3. -/
def C3T21 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 5) | 2 => (-29 / 60) | 3 => (-197 / 380) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24 / 25) | 2 => (-3781 / 3600) | 3 => (-465647 / 433200) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-85532647 / 98587200) | 3, 1 => (-4159379 / 13144960) | 3, 2 => (-8273 / 43240) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (85532647 / 98587200) | 3, 1 => (4159379 / 13144960) | 3, 2 => (8273 / 43240) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C3T21_ok : C3T21.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T21_den : ℕ := 197174400
theorem C3T21_den_ok :
    (∀ d ∈ C3T21.R, ∀ e ∈ C3T21.R, (C3T21.Lq d e).den ∣ C3T21_den ∧ (C3T21.Lq' d e).den ∣ C3T21_den) ∧
    (∀ d ∈ C3T21.C, ∀ e ∈ C3T21.C, (C3T21.Pq d e).den ∣ C3T21_den ∧ (C3T21.Pq' d e).den ∣ C3T21_den) := by
  constructor <;> decide +kernel
theorem C3T21_rload_3 : C3T21.rload 3 = ((-74006459 / 197174400), (-29514697 / 98587200)) := by decide +kernel
#print axioms C3T21_ok
#print axioms C3T21_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
