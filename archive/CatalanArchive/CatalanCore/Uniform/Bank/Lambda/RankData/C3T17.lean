import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 6c880ae76c3b17b3166095be1e0ff61aa71db2a33b560fac696f8f75100b1c37, root class 3. -/
def C3T17 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 3) | 2 => (-17 / 42) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-7 / 9) | 2 => (-1507 / 1764) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T17_ok : C3T17.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T17_den : ℕ := 1
theorem C3T17_den_ok :
    (∀ d ∈ C3T17.R, ∀ e ∈ C3T17.R, (C3T17.Lq d e).den ∣ C3T17_den ∧ (C3T17.Lq' d e).den ∣ C3T17_den) ∧
    (∀ d ∈ C3T17.C, ∀ e ∈ C3T17.C, (C3T17.Pq d e).den ∣ C3T17_den ∧ (C3T17.Pq' d e).den ∣ C3T17_den) := by
  constructor <;> decide +kernel
#print axioms C3T17_ok
#print axioms C3T17_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
