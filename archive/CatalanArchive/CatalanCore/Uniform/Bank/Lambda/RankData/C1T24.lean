import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 147a120e3a7c06e93819fa1909444c2d4c0b52cebd9fcef3d37dc4da8772d365, root class 1. -/
def C1T24 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => (-4) | 1 => (-19 / 5) | _ => 0
  ee := fun d => match d with | 0 => (-16) | 1 => (-391 / 25) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (-1 / 80) | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (1 / 80) | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C1T24_ok : C1T24.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T24_den : ℕ := 80
theorem C1T24_den_ok :
    (∀ d ∈ C1T24.R, ∀ e ∈ C1T24.R, (C1T24.Lq d e).den ∣ C1T24_den ∧ (C1T24.Lq' d e).den ∣ C1T24_den) ∧
    (∀ d ∈ C1T24.C, ∀ e ∈ C1T24.C, (C1T24.Pq d e).den ∣ C1T24_den ∧ (C1T24.Pq' d e).den ∣ C1T24_den) := by
  constructor <;> decide +kernel
theorem C1T24_rload_1 : C1T24.rload 1 = ((79 / 80), (-15 / 4)) := by decide +kernel
#print axioms C1T24_ok
#print axioms C1T24_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
