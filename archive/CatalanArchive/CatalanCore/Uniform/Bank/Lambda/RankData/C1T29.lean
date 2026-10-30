import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type e46f9710ca9cf235f917efa9f6093daa4a5dc3c5bc568b2981a525e86c19980d, root class 1. -/
def C1T29 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => 0 | _ => 0
  ee := fun d => match d with | 0 => 0 | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {0}
  kc := {0}

theorem C1T29_ok : C1T29.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T29_den : ℕ := 1
theorem C1T29_den_ok :
    (∀ d ∈ C1T29.R, ∀ e ∈ C1T29.R, (C1T29.Lq d e).den ∣ C1T29_den ∧ (C1T29.Lq' d e).den ∣ C1T29_den) ∧
    (∀ d ∈ C1T29.C, ∀ e ∈ C1T29.C, (C1T29.Pq d e).den ∣ C1T29_den ∧ (C1T29.Pq' d e).den ∣ C1T29_den) := by
  constructor <;> decide +kernel
theorem C1T29_rload_0 : C1T29.rload 0 = (1, 0) := by decide +kernel
theorem C1T29_cload_0 : C1T29.cload 0 = (1, 0) := by decide +kernel
#print axioms C1T29_ok
#print axioms C1T29_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
