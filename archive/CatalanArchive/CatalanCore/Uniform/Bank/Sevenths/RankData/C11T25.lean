import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c439fa9bf86baa392f46ac03012b0ca3996246bd92b85f9c8d86149589a307a5, root class 11. -/
def C11T25 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | 2 => (-25 / 9) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | 2 => (-940 / 81) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C11T25_ok : C11T25.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T25_den : ℕ := 1
theorem C11T25_den_ok :
    (∀ d ∈ C11T25.R, ∀ e ∈ C11T25.R, (C11T25.Lq d e).den ∣ C11T25_den ∧ (C11T25.Lq' d e).den ∣ C11T25_den) ∧
    (∀ d ∈ C11T25.C, ∀ e ∈ C11T25.C, (C11T25.Pq d e).den ∣ C11T25_den ∧ (C11T25.Pq' d e).den ∣ C11T25_den) := by
  constructor <;> decide +kernel
#print axioms C11T25_ok
#print axioms C11T25_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
