import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 3d7428c2d156992d1236263dead4883588828c9cf66842b3ba1dbc2fa5bc461e, root class 13. -/
def C13T17 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | 2 => (-8 / 39) | 3 => (-173 / 780) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | 2 => (-610 / 1521) | 3 => (-27881 / 67600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C13T17_ok : C13T17.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T17_den : ℕ := 1
theorem C13T17_den_ok :
    (∀ d ∈ C13T17.R, ∀ e ∈ C13T17.R, (C13T17.Lq d e).den ∣ C13T17_den ∧ (C13T17.Lq' d e).den ∣ C13T17_den) ∧
    (∀ d ∈ C13T17.C, ∀ e ∈ C13T17.C, (C13T17.Pq d e).den ∣ C13T17_den ∧ (C13T17.Pq' d e).den ∣ C13T17_den) := by
  constructor <;> decide +kernel
#print axioms C13T17_ok
#print axioms C13T17_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
