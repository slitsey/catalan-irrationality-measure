import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 886f8d4b4a2ca677518627c8d21ccff670b86df631e38b44bf8451f42749eb97, root class 9. -/
def C9T26 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-159 / 88) | 2, 1 => (-13 / 22) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (159 / 88) | 2, 1 => (13 / 22) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C9T26_ok : C9T26.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T26_den : ℕ := 88
theorem C9T26_den_ok :
    (∀ d ∈ C9T26.R, ∀ e ∈ C9T26.R, (C9T26.Lq d e).den ∣ C9T26_den ∧ (C9T26.Lq' d e).den ∣ C9T26_den) ∧
    (∀ d ∈ C9T26.C, ∀ e ∈ C9T26.C, (C9T26.Pq d e).den ∣ C9T26_den ∧ (C9T26.Pq' d e).den ∣ C9T26_den) := by
  constructor <;> decide +kernel
theorem C9T26_rload_2 : C9T26.rload 2 = ((-123 / 88), (-39 / 88)) := by decide +kernel
#print axioms C9T26_ok
#print axioms C9T26_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
