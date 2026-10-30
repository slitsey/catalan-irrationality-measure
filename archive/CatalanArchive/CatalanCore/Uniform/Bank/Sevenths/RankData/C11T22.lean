import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d2386093839e12b795885c2d5e4f3f52dfdfe64fa432142e5792207c31846b0d, root class 11. -/
def C11T22 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | 2 => (-25 / 9) | 3 => (-415 / 144) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | 2 => (-940 / 81) | 3 => (-242305 / 20736) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-148543 / 107676) | 3, 1 => (-21077 / 71784) | 3, 2 => (-488 / 2991) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (148543 / 107676) | 3, 1 => (21077 / 71784) | 3, 2 => (488 / 2991) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C11T22_ok : C11T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T22_den : ℕ := 215352
theorem C11T22_den_ok :
    (∀ d ∈ C11T22.R, ∀ e ∈ C11T22.R, (C11T22.Lq d e).den ∣ C11T22_den ∧ (C11T22.Lq' d e).den ∣ C11T22_den) ∧
    (∀ d ∈ C11T22.C, ∀ e ∈ C11T22.C, (C11T22.Pq d e).den ∣ C11T22_den ∧ (C11T22.Pq' d e).den ∣ C11T22_den) := by
  constructor <;> decide +kernel
theorem C11T22_rload_3 : C11T22.rload 3 = ((-180101 / 215352), (-364955 / 215352)) := by decide +kernel
#print axioms C11T22_ok
#print axioms C11T22_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
