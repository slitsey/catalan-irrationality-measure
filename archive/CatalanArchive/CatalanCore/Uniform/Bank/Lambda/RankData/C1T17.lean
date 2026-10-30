import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 34b5d2f5ee3c9bca5c73d7ae5bac836df900b787aef82e08ef24a359eb68594b, root class 1. -/
def C1T17 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-4) | 1 => (-19 / 5) | 2 => (-337 / 90) | _ => 0
  ee := fun d => match d with | 0 => (-16) | 1 => (-391 / 25) | 2 => (-126259 / 8100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-2981 / 375300) | 2, 1 => (-259 / 75060) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (2981 / 375300) | 2, 1 => (259 / 75060) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C1T17_ok : C1T17.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T17_den : ℕ := 375300
theorem C1T17_den_ok :
    (∀ d ∈ C1T17.R, ∀ e ∈ C1T17.R, (C1T17.Lq d e).den ∣ C1T17_den ∧ (C1T17.Lq' d e).den ∣ C1T17_den) ∧
    (∀ d ∈ C1T17.C, ∀ e ∈ C1T17.C, (C1T17.Pq d e).den ∣ C1T17_den ∧ (C1T17.Pq' d e).den ∣ C1T17_den) := by
  constructor <;> decide +kernel
theorem C1T17_rload_2 : C1T17.rload 2 = ((92756 / 93825), (-92563 / 25020)) := by decide +kernel
#print axioms C1T17_ok
#print axioms C1T17_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
