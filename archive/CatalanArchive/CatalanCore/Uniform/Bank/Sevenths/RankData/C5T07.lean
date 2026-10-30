import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 21382e43da3535a3e21e69f8c1b4f2daf04987337de419da5bb41cc0d3695767, root class 5. -/
def C5T07 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | 2 => (-23 / 15) | 3 => (-137 / 85) | 4 => (-3373 / 2040) | 5 => (-21239 / 12648) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | 2 => (-1054 / 225) | 3 => (-102802 / 21675) | 4 => (-19831909 / 4161600) | 5 => (-3820482209 / 799859520) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C5T07_ok : C5T07.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T07_den : ℕ := 1
theorem C5T07_den_ok :
    (∀ d ∈ C5T07.R, ∀ e ∈ C5T07.R, (C5T07.Lq d e).den ∣ C5T07_den ∧ (C5T07.Lq' d e).den ∣ C5T07_den) ∧
    (∀ d ∈ C5T07.C, ∀ e ∈ C5T07.C, (C5T07.Pq d e).den ∣ C5T07_den ∧ (C5T07.Pq' d e).den ∣ C5T07_den) := by
  constructor <;> decide +kernel
#print axioms C5T07_ok
#print axioms C5T07_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
