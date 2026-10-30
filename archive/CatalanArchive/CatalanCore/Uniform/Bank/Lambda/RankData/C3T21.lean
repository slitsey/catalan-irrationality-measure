import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 8c835e32a32fc97967c9f42d6e3c78cb4181f7f26ced91e3e08d0aef7efeadf5, root class 3. -/
def C3T21 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 3) | 2 => (-17 / 42) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-7 / 9) | 2 => (-1507 / 1764) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-137 / 84) | 1, 1 => 1 | 1, 2 => (-17 / 28) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (137 / 84) | 1, 1 => 1 | 1, 2 => (17 / 28) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C3T21_ok : C3T21.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T21_den : ℕ := 84
theorem C3T21_den_ok :
    (∀ d ∈ C3T21.R, ∀ e ∈ C3T21.R, (C3T21.Lq d e).den ∣ C3T21_den ∧ (C3T21.Lq' d e).den ∣ C3T21_den) ∧
    (∀ d ∈ C3T21.C, ∀ e ∈ C3T21.C, (C3T21.Pq d e).den ∣ C3T21_den ∧ (C3T21.Pq' d e).den ∣ C3T21_den) := by
  constructor <;> decide +kernel
theorem C3T21_cload_2 : C3T21.cload 2 = ((-26 / 21), (-17 / 84)) := by decide +kernel
#print axioms C3T21_ok
#print axioms C3T21_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
