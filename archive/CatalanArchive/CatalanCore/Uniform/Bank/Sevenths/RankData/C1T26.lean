import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 9caea4c8230ef9266ba34d504d37091000b4d3e38f4986defa9a5278535e18b3, root class 1. -/
def C1T26 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7) | 1 => (-55 / 8) | _ => 0
  ee := fun d => match d with | 0 => (-49) | 1 => (-3121 / 64) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T26_ok : C1T26.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T26_den : ℕ := 1
theorem C1T26_den_ok :
    (∀ d ∈ C1T26.R, ∀ e ∈ C1T26.R, (C1T26.Lq d e).den ∣ C1T26_den ∧ (C1T26.Lq' d e).den ∣ C1T26_den) ∧
    (∀ d ∈ C1T26.C, ∀ e ∈ C1T26.C, (C1T26.Pq d e).den ∣ C1T26_den ∧ (C1T26.Pq' d e).den ∣ C1T26_den) := by
  constructor <;> decide +kernel
#print axioms C1T26_ok
#print axioms C1T26_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
