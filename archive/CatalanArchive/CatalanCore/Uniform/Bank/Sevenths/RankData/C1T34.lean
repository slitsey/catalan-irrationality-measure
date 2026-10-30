import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type e3013739b42322aa0198f3f027d0075767f540c76f4ccd1bdf98547590d4f136, root class 1. -/
def C1T34 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | _ => 0
  Lq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C1T34_ok : C1T34.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T34_den : ℕ := 1
theorem C1T34_den_ok :
    (∀ d ∈ C1T34.R, ∀ e ∈ C1T34.R, (C1T34.Lq d e).den ∣ C1T34_den ∧ (C1T34.Lq' d e).den ∣ C1T34_den) ∧
    (∀ d ∈ C1T34.C, ∀ e ∈ C1T34.C, (C1T34.Pq d e).den ∣ C1T34_den ∧ (C1T34.Pq' d e).den ∣ C1T34_den) := by
  constructor <;> decide +kernel
theorem C1T34_rload_1 : C1T34.rload 1 = (1, 0) := by decide +kernel
#print axioms C1T34_ok
#print axioms C1T34_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
