import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 424a443eb8726bf7c378ea1e1705ec20583cbd3969a48e927b9ff478b13d0bd4, root class 5. -/
def C5T23 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | 2 => (-496 / 255) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | 2 => (-315631 / 65025) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-1282527 / 36869600) | 2, 1 => (-58131 / 3686960) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (1282527 / 36869600) | 2, 1 => (58131 / 3686960) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C5T23_ok : C5T23.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T23_den : ℕ := 36869600
theorem C5T23_den_ok :
    (∀ d ∈ C5T23.R, ∀ e ∈ C5T23.R, (C5T23.Lq d e).den ∣ C5T23_den ∧ (C5T23.Lq' d e).den ∣ C5T23_den) ∧
    (∀ d ∈ C5T23.C, ∀ e ∈ C5T23.C, (C5T23.Pq d e).den ∣ C5T23_den ∧ (C5T23.Pq' d e).den ∣ C5T23_den) := by
  constructor <;> decide +kernel
theorem C5T23_rload_2 : C5T23.rload 2 = ((35005763 / 36869600), (-1266383 / 691305)) := by decide +kernel
#print axioms C5T23_ok
#print axioms C5T23_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
