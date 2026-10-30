import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 16b32fab2ef1b3caecd67509bb6ffc424ea59fd15b72bdb9e2caae06b5e13305, root class 5. -/
def C5T20 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | 2 => (-23 / 15) | 3 => (-137 / 85) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | 2 => (-1054 / 225) | 3 => (-102802 / 21675) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-25494599 / 23441640) | 1, 1 => 1 | 1, 3 => (-946379 / 3125552) | 2, 2 => 1 | 2, 3 => (-4003 / 22982) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (25494599 / 23441640) | 1, 1 => 1 | 1, 3 => (946379 / 3125552) | 2, 2 => 1 | 2, 3 => (4003 / 22982) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C5T20_ok : C5T20.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T20_den : ℕ := 46883280
theorem C5T20_den_ok :
    (∀ d ∈ C5T20.R, ∀ e ∈ C5T20.R, (C5T20.Lq d e).den ∣ C5T20_den ∧ (C5T20.Lq' d e).den ∣ C5T20_den) ∧
    (∀ d ∈ C5T20.C, ∀ e ∈ C5T20.C, (C5T20.Pq d e).den ∣ C5T20_den ∧ (C5T20.Pq' d e).den ∣ C5T20_den) := by
  constructor <;> decide +kernel
theorem C5T20_cload_3 : C5T20.cload 3 = ((-26467723 / 46883280), (-3676321 / 3906940)) := by decide +kernel
#print axioms C5T20_ok
#print axioms C5T20_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
