import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 152ea4a5fce18f9c1a436d49390f537937e0a432e096896e9d16c1e61e4df151, root class 11. -/
def C11T27 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | 2 => (-25 / 9) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | 2 => (-940 / 81) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-47 / 18) | 2, 1 => (-5 / 9) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (47 / 18) | 2, 1 => (5 / 9) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C11T27_ok : C11T27.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T27_den : ℕ := 18
theorem C11T27_den_ok :
    (∀ d ∈ C11T27.R, ∀ e ∈ C11T27.R, (C11T27.Lq d e).den ∣ C11T27_den ∧ (C11T27.Lq' d e).den ∣ C11T27_den) ∧
    (∀ d ∈ C11T27.C, ∀ e ∈ C11T27.C, (C11T27.Pq d e).den ∣ C11T27_den ∧ (C11T27.Pq' d e).den ∣ C11T27_den) := by
  constructor <;> decide +kernel
theorem C11T27_rload_2 : C11T27.rload 2 = ((-13 / 6), (-25 / 18)) := by decide +kernel
#print axioms C11T27_ok
#print axioms C11T27_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
