import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type fb7d5a88369b0cb1f46c5bf6e7d6c185afe23bf821c058886eb9d888c18d8c52, root class 9. -/
def C9T15 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | 3 => (-373 / 396) | 4 => (-4811 / 4950) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | 3 => (-354025 / 156816) | 4 => (-13926499 / 6125625) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-846596363474207 / 1305183761654850) | 1, 1 => 1 | 1, 4 => (-19806504172274 / 93227411546775) | 2, 2 => 1 | 2, 4 => (-22361730766621 / 177979603862025) | 3, 3 => 1 | 3, 4 => (-195653447362 / 2197279060025) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (846596363474207 / 1305183761654850) | 1, 1 => 1 | 1, 4 => (19806504172274 / 93227411546775) | 2, 2 => 1 | 2, 4 => (22361730766621 / 177979603862025) | 3, 3 => 1 | 3, 4 => (195653447362 / 2197279060025) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C9T15_ok : C9T15.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T15_den : ℕ := 3915551284964550
theorem C9T15_den_ok :
    (∀ d ∈ C9T15.R, ∀ e ∈ C9T15.R, (C9T15.Lq d e).den ∣ C9T15_den ∧ (C9T15.Lq' d e).den ∣ C9T15_den) ∧
    (∀ d ∈ C9T15.C, ∀ e ∈ C9T15.C, (C9T15.Pq d e).den ∣ C9T15_den ∧ (C9T15.Pq' d e).den ∣ C9T15_den) := by
  constructor <;> decide +kernel
theorem C9T15_cload_4 : C9T15.cload 4 = ((-11868940030333 / 156622051398582), (-1611490998685361 / 2610367523309700)) := by decide +kernel
#print axioms C9T15_ok
#print axioms C9T15_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
