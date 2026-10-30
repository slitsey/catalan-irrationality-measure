import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 8cb4c6728e8bb6357e62fb2c0c75d56e39fa739e0232d77c83f085ff0f3c9a61, root class 5. -/
def C5T27 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | 2 => (-23 / 15) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | 2 => (-1054 / 225) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-31 / 15) | 2, 1 => (-23 / 40) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (31 / 15) | 2, 1 => (23 / 40) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C5T27_ok : C5T27.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T27_den : ℕ := 120
theorem C5T27_den_ok :
    (∀ d ∈ C5T27.R, ∀ e ∈ C5T27.R, (C5T27.Lq d e).den ∣ C5T27_den ∧ (C5T27.Lq' d e).den ∣ C5T27_den) ∧
    (∀ d ∈ C5T27.C, ∀ e ∈ C5T27.C, (C5T27.Pq d e).den ∣ C5T27_den ∧ (C5T27.Pq' d e).den ∣ C5T27_den) := by
  constructor <;> decide +kernel
theorem C5T27_rload_2 : C5T27.rload 2 = ((-197 / 120), (-23 / 30)) := by decide +kernel
#print axioms C5T27_ok
#print axioms C5T27_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
