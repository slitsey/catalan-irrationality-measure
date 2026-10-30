import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 96d9d2b578a84a0b4732b06770eefd96c79df9eecbe8ecdbf1d2b64ecf3cdfc3, root class 5. -/
def C5T24 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | 2 => (-496 / 255) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | 2 => (-315631 / 65025) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-1282527 / 36869600) | 1, 1 => 1 | 1, 2 => (-58131 / 3686960) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (1282527 / 36869600) | 1, 1 => 1 | 1, 2 => (58131 / 3686960) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C5T24_ok : C5T24.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T24_den : ℕ := 36869600
theorem C5T24_den_ok :
    (∀ d ∈ C5T24.R, ∀ e ∈ C5T24.R, (C5T24.Lq d e).den ∣ C5T24_den ∧ (C5T24.Lq' d e).den ∣ C5T24_den) ∧
    (∀ d ∈ C5T24.C, ∀ e ∈ C5T24.C, (C5T24.Pq d e).den ∣ C5T24_den ∧ (C5T24.Pq' d e).den ∣ C5T24_den) := by
  constructor <;> decide +kernel
theorem C5T24_cload_2 : C5T24.cload 2 = ((35005763 / 36869600), (-1266383 / 691305)) := by decide +kernel
#print axioms C5T24_ok
#print axioms C5T24_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
