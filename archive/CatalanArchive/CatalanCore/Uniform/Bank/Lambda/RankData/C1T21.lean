import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 617b967e3c6e923fe0cf80070087bea8018674d8ce0f23f2be45e3bf835e4238, root class 1. -/
def C1T21 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-3) | 2 => (-33 / 10) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-15) | 2 => (-1539 / 100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-57 / 20) | 2, 1 => (-11 / 20) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (57 / 20) | 2, 1 => (11 / 20) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C1T21_ok : C1T21.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T21_den : ℕ := 20
theorem C1T21_den_ok :
    (∀ d ∈ C1T21.R, ∀ e ∈ C1T21.R, (C1T21.Lq d e).den ∣ C1T21_den ∧ (C1T21.Lq' d e).den ∣ C1T21_den) ∧
    (∀ d ∈ C1T21.C, ∀ e ∈ C1T21.C, (C1T21.Pq d e).den ∣ C1T21_den ∧ (C1T21.Pq' d e).den ∣ C1T21_den) := by
  constructor <;> decide +kernel
theorem C1T21_rload_2 : C1T21.rload 2 = ((-12 / 5), (-33 / 20)) := by decide +kernel
#print axioms C1T21_ok
#print axioms C1T21_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
