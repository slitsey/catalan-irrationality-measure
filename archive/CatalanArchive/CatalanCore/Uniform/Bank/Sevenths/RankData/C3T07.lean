import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 2416d511daf911e353b6fba737f346b99c5c618e1d5c532171995e68772db9dc, root class 3. -/
def C3T07 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 5) | 2 => (-29 / 60) | 3 => (-197 / 380) | 4 => (-664 / 1235) | 5 => (-22406 / 40755) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24 / 25) | 2 => (-3781 / 3600) | 3 => (-465647 / 433200) | 4 => (-9928171 / 9151350) | 5 => (-3620520521 / 3321940050) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
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
end CatalanCore.Uniform.Bank.Sevenths.RankData
