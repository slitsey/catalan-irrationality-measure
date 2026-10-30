import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d0cbdf01b2c719f57131416c2073f47802c2849b5d4444f6b7ff20e42bd8ae0b, root class 1. -/
def C1T30 : FibreCert where
  R := {0}
  C := ∅
  lf := fun d => match d with | 0 => (-4) | _ => 0
  ee := fun d => match d with | 0 => (-16) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun _ _ => 0
  Pq' := fun _ _ => 0
  kr := {0}
  kc := ∅

theorem C1T30_ok : C1T30.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T30_den : ℕ := 1
theorem C1T30_den_ok :
    (∀ d ∈ C1T30.R, ∀ e ∈ C1T30.R, (C1T30.Lq d e).den ∣ C1T30_den ∧ (C1T30.Lq' d e).den ∣ C1T30_den) ∧
    (∀ d ∈ C1T30.C, ∀ e ∈ C1T30.C, (C1T30.Pq d e).den ∣ C1T30_den ∧ (C1T30.Pq' d e).den ∣ C1T30_den) := by
  constructor <;> decide +kernel
theorem C1T30_rload_0 : C1T30.rload 0 = (1, (-4)) := by decide +kernel
#print axioms C1T30_ok
#print axioms C1T30_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
