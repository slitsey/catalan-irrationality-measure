import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 442bcef536a03ec793463852bee01251d02dbeeb0fa1941409d8862f67d1fa46, root class 1. -/
def C1T29 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7) | 1 => (-55 / 8) | _ => 0
  ee := fun d => match d with | 0 => (-49) | 1 => (-3121 / 64) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (-1 / 392) | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (1 / 392) | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C1T29_ok : C1T29.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T29_den : ℕ := 392
theorem C1T29_den_ok :
    (∀ d ∈ C1T29.R, ∀ e ∈ C1T29.R, (C1T29.Lq d e).den ∣ C1T29_den ∧ (C1T29.Lq' d e).den ∣ C1T29_den) ∧
    (∀ d ∈ C1T29.C, ∀ e ∈ C1T29.C, (C1T29.Pq d e).den ∣ C1T29_den ∧ (C1T29.Pq' d e).den ∣ C1T29_den) := by
  constructor <;> decide +kernel
theorem C1T29_cload_1 : C1T29.cload 1 = ((391 / 392), (-48 / 7)) := by decide +kernel
#print axioms C1T29_ok
#print axioms C1T29_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
