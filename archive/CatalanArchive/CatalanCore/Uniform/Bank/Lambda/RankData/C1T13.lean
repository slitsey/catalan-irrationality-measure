import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type a4fa70470e6202e6a8102cd38a03239083a3b6fd48fd0444d98152b4fe5108f2, root class 1. -/
def C1T13 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-3) | 2 => (-33 / 10) | 3 => (-307 / 90) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-15) | 2 => (-1539 / 100) | 3 => (-125359 / 8100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T13_ok : C1T13.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T13_den : ℕ := 1
theorem C1T13_den_ok :
    (∀ d ∈ C1T13.R, ∀ e ∈ C1T13.R, (C1T13.Lq d e).den ∣ C1T13_den ∧ (C1T13.Lq' d e).den ∣ C1T13_den) ∧
    (∀ d ∈ C1T13.C, ∀ e ∈ C1T13.C, (C1T13.Pq d e).den ∣ C1T13_den ∧ (C1T13.Pq' d e).den ∣ C1T13_den) := by
  constructor <;> decide +kernel
#print axioms C1T13_ok
#print axioms C1T13_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
