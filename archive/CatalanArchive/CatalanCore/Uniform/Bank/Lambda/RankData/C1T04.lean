import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type beb7366a95014bc8727439b489578a5122715cc8290376791fc5dbdfb7629dae, root class 1. -/
def C1T04 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-4) | 1 => (-19 / 5) | 2 => (-337 / 90) | 3 => (-4351 / 1170) | 4 => (-147349 / 39780) | _ => 0
  ee := fun d => match d with | 0 => (-16) | 1 => (-391 / 25) | 2 => (-126259 / 8100) | 3 => (-21315271 / 1368900) | 4 => (-24629159851 / 1582448400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T04_ok : C1T04.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T04_den : ℕ := 1
theorem C1T04_den_ok :
    (∀ d ∈ C1T04.R, ∀ e ∈ C1T04.R, (C1T04.Lq d e).den ∣ C1T04_den ∧ (C1T04.Lq' d e).den ∣ C1T04_den) ∧
    (∀ d ∈ C1T04.C, ∀ e ∈ C1T04.C, (C1T04.Pq d e).den ∣ C1T04_den ∧ (C1T04.Pq' d e).den ∣ C1T04_den) := by
  constructor <;> decide +kernel
#print axioms C1T04_ok
#print axioms C1T04_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
