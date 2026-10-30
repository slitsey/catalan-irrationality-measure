import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type bdeb7d33ec5dfd797f5841ed7a4a78ca1df155384d593d38edf2af64ca492e64, root class 9. -/
def C9T14 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | 3 => (-373 / 396) | 4 => (-4811 / 4950) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | 3 => (-354025 / 156816) | 4 => (-13926499 / 6125625) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-846596363474207 / 1305183761654850) | 4, 1 => (-19806504172274 / 93227411546775) | 4, 2 => (-22361730766621 / 177979603862025) | 4, 3 => (-195653447362 / 2197279060025) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (846596363474207 / 1305183761654850) | 4, 1 => (19806504172274 / 93227411546775) | 4, 2 => (22361730766621 / 177979603862025) | 4, 3 => (195653447362 / 2197279060025) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C9T14_ok : C9T14.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T14_den : ℕ := 3915551284964550
theorem C9T14_den_ok :
    (∀ d ∈ C9T14.R, ∀ e ∈ C9T14.R, (C9T14.Lq d e).den ∣ C9T14_den ∧ (C9T14.Lq' d e).den ∣ C9T14_den) ∧
    (∀ d ∈ C9T14.C, ∀ e ∈ C9T14.C, (C9T14.Pq d e).den ∣ C9T14_den ∧ (C9T14.Pq' d e).den ∣ C9T14_den) := by
  constructor <;> decide +kernel
theorem C9T14_rload_4 : C9T14.rload 4 = ((-11868940030333 / 156622051398582), (-1611490998685361 / 2610367523309700)) := by decide +kernel
#print axioms C9T14_ok
#print axioms C9T14_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
