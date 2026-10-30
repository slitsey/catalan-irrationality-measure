import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 774275699b6dda147763ef4374efb6318511b777951217070a80f318693068f0, root class 11. -/
def C11T13 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | 2 => (-25 / 9) | 3 => (-415 / 144) | 4 => (-9725 / 3312) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | 2 => (-940 / 81) | 3 => (-242305 / 20736) | 4 => (-128509825 / 10969344) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C11T13_ok : C11T13.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T13_den : ℕ := 1
theorem C11T13_den_ok :
    (∀ d ∈ C11T13.R, ∀ e ∈ C11T13.R, (C11T13.Lq d e).den ∣ C11T13_den ∧ (C11T13.Lq' d e).den ∣ C11T13_den) ∧
    (∀ d ∈ C11T13.C, ∀ e ∈ C11T13.C, (C11T13.Pq d e).den ∣ C11T13_den ∧ (C11T13.Pq' d e).den ∣ C11T13_den) := by
  constructor <;> decide +kernel
#print axioms C11T13_ok
#print axioms C11T13_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
