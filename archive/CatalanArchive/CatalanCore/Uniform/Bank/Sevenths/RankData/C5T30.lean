import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 892543e06ad20e3d4d9101c87faf1b86a9bc8358ba962e0c43f71517c4874b48, root class 5. -/
def C5T30 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (-27 / 490) | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (27 / 490) | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C5T30_ok : C5T30.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T30_den : ℕ := 490
theorem C5T30_den_ok :
    (∀ d ∈ C5T30.R, ∀ e ∈ C5T30.R, (C5T30.Lq d e).den ∣ C5T30_den ∧ (C5T30.Lq' d e).den ∣ C5T30_den) ∧
    (∀ d ∈ C5T30.C, ∀ e ∈ C5T30.C, (C5T30.Pq d e).den ∣ C5T30_den ∧ (C5T30.Pq' d e).den ∣ C5T30_den) := by
  constructor <;> decide +kernel
theorem C5T30_cload_1 : C5T30.cload 1 = ((463 / 490), (-40 / 21)) := by decide +kernel
#print axioms C5T30_ok
#print axioms C5T30_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
