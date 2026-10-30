import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 7f96c136849d4908bf78ef640087a87805a20ed3e730105f3f906ede6ad72e67, root class 5. -/
def C5T21 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | 2 => (-23 / 15) | 3 => (-137 / 85) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | 2 => (-1054 / 225) | 3 => (-102802 / 21675) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-25494599 / 23441640) | 3, 1 => (-946379 / 3125552) | 3, 2 => (-4003 / 22982) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (25494599 / 23441640) | 3, 1 => (946379 / 3125552) | 3, 2 => (4003 / 22982) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C5T21_ok : C5T21.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T21_den : ℕ := 46883280
theorem C5T21_den_ok :
    (∀ d ∈ C5T21.R, ∀ e ∈ C5T21.R, (C5T21.Lq d e).den ∣ C5T21_den ∧ (C5T21.Lq' d e).den ∣ C5T21_den) ∧
    (∀ d ∈ C5T21.C, ∀ e ∈ C5T21.C, (C5T21.Pq d e).den ∣ C5T21_den ∧ (C5T21.Pq' d e).den ∣ C5T21_den) := by
  constructor <;> decide +kernel
theorem C5T21_rload_3 : C5T21.rload 3 = ((-26467723 / 46883280), (-3676321 / 3906940)) := by decide +kernel
#print axioms C5T21_ok
#print axioms C5T21_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
