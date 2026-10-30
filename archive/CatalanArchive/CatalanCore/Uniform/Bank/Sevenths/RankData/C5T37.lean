import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 7d76ed8e45889c2e0d10f13ba596156292eb9abc997be00567bdeccbc23627c7, root class 5. -/
def C5T37 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 3) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C5T37_ok : C5T37.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T37_den : ℕ := 1
theorem C5T37_den_ok :
    (∀ d ∈ C5T37.R, ∀ e ∈ C5T37.R, (C5T37.Lq d e).den ∣ C5T37_den ∧ (C5T37.Lq' d e).den ∣ C5T37_den) ∧
    (∀ d ∈ C5T37.C, ∀ e ∈ C5T37.C, (C5T37.Pq d e).den ∣ C5T37_den ∧ (C5T37.Pq' d e).den ∣ C5T37_den) := by
  constructor <;> decide +kernel
theorem C5T37_cload_0 : C5T37.cload 0 = (1, (-7 / 3)) := by decide +kernel
#print axioms C5T37_ok
#print axioms C5T37_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
