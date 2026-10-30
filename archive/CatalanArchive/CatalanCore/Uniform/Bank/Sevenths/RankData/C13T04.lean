import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d25ed2eadec260da4d703809fb33254aa01454240cbb31c96e32792f57511a10, root class 13. -/
def C13T04 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => (-7 / 6) | 1 => (-55 / 78) | 2 => (-433 / 780) | 3 => (-3377 / 7020) | 4 => (-13036 / 29835) | 5 => (-498674 / 1223235) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | 1 => (-3961 / 6084) | 2 => (-318529 / 608400) | 3 => (-23637649 / 49280400) | 4 => (-1636209559 / 3560508900) | 5 => (-2685524586343 / 5985215460900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C13T04_ok : C13T04.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T04_den : ℕ := 1
theorem C13T04_den_ok :
    (∀ d ∈ C13T04.R, ∀ e ∈ C13T04.R, (C13T04.Lq d e).den ∣ C13T04_den ∧ (C13T04.Lq' d e).den ∣ C13T04_den) ∧
    (∀ d ∈ C13T04.C, ∀ e ∈ C13T04.C, (C13T04.Pq d e).den ∣ C13T04_den ∧ (C13T04.Pq' d e).den ∣ C13T04_den) := by
  constructor <;> decide +kernel
#print axioms C13T04_ok
#print axioms C13T04_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
