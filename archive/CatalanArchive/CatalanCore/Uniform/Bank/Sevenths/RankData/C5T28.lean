import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 78a31f56ca5d28aaed97df1a9c6e0af3dc174621e2712a85148468991468668c, root class 5. -/
def C5T28 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | 2 => (-23 / 15) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | 2 => (-1054 / 225) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-31 / 15) | 1, 1 => 1 | 1, 2 => (-23 / 40) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (31 / 15) | 1, 1 => 1 | 1, 2 => (23 / 40) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C5T28_ok : C5T28.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T28_den : ℕ := 120
theorem C5T28_den_ok :
    (∀ d ∈ C5T28.R, ∀ e ∈ C5T28.R, (C5T28.Lq d e).den ∣ C5T28_den ∧ (C5T28.Lq' d e).den ∣ C5T28_den) ∧
    (∀ d ∈ C5T28.C, ∀ e ∈ C5T28.C, (C5T28.Pq d e).den ∣ C5T28_den ∧ (C5T28.Pq' d e).den ∣ C5T28_den) := by
  constructor <;> decide +kernel
theorem C5T28_cload_2 : C5T28.cload 2 = ((-197 / 120), (-23 / 30)) := by decide +kernel
#print axioms C5T28_ok
#print axioms C5T28_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
