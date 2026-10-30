import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 75888ba6072da2abcc79ea5d764e3b7506d918da00ed03729f8ff6258c1014b3, root class 11. -/
def C11T19 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | 2 => (-25 / 9) | 3 => (-415 / 144) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | 2 => (-940 / 81) | 3 => (-242305 / 20736) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C11T19_ok : C11T19.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T19_den : ℕ := 1
theorem C11T19_den_ok :
    (∀ d ∈ C11T19.R, ∀ e ∈ C11T19.R, (C11T19.Lq d e).den ∣ C11T19_den ∧ (C11T19.Lq' d e).den ∣ C11T19_den) ∧
    (∀ d ∈ C11T19.C, ∀ e ∈ C11T19.C, (C11T19.Pq d e).den ∣ C11T19_den ∧ (C11T19.Pq' d e).den ∣ C11T19_den) := by
  constructor <;> decide +kernel
#print axioms C11T19_ok
#print axioms C11T19_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
