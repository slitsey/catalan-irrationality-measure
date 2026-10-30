import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 6f850ee7f8e5290f203216ad787ced72b46005273606f5770bee1d5ca007fe55, root class 11. -/
def C11T21 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | 2 => (-25 / 9) | 3 => (-415 / 144) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | 2 => (-940 / 81) | 3 => (-242305 / 20736) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-148543 / 107676) | 1, 1 => 1 | 1, 3 => (-21077 / 71784) | 2, 2 => 1 | 2, 3 => (-488 / 2991) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (148543 / 107676) | 1, 1 => 1 | 1, 3 => (21077 / 71784) | 2, 2 => 1 | 2, 3 => (488 / 2991) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C11T21_ok : C11T21.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T21_den : ℕ := 215352
theorem C11T21_den_ok :
    (∀ d ∈ C11T21.R, ∀ e ∈ C11T21.R, (C11T21.Lq d e).den ∣ C11T21_den ∧ (C11T21.Lq' d e).den ∣ C11T21_den) ∧
    (∀ d ∈ C11T21.C, ∀ e ∈ C11T21.C, (C11T21.Pq d e).den ∣ C11T21_den ∧ (C11T21.Pq' d e).den ∣ C11T21_den) := by
  constructor <;> decide +kernel
theorem C11T21_cload_3 : C11T21.cload 3 = ((-180101 / 215352), (-364955 / 215352)) := by decide +kernel
#print axioms C11T21_ok
#print axioms C11T21_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
