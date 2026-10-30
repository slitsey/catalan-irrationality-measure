import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 848de9cd3cd63a747ddc15b637e6f0d35f2409f18ed2f4ace2998a24f619def6, root class 3. -/
def C3T22 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 5) | 1 => (-59 / 60) | 2 => (-971 / 1140) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | 1 => (-4681 / 3600) | 2 => (-1541341 / 1299600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T22_ok : C3T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T22_den : ℕ := 1
theorem C3T22_den_ok :
    (∀ d ∈ C3T22.R, ∀ e ∈ C3T22.R, (C3T22.Lq d e).den ∣ C3T22_den ∧ (C3T22.Lq' d e).den ∣ C3T22_den) ∧
    (∀ d ∈ C3T22.C, ∀ e ∈ C3T22.C, (C3T22.Pq d e).den ∣ C3T22_den ∧ (C3T22.Pq' d e).den ∣ C3T22_den) := by
  constructor <;> decide +kernel
#print axioms C3T22_ok
#print axioms C3T22_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
