import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 98bf79c9a9f3a6c65bac13643b689b4880dc07e35e682fa1697c6caa20f2f4e5, root class 11. -/
def C11T04 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => (-7 / 2) | 1 => (-59 / 18) | 2 => (-463 / 144) | 3 => (-10553 / 3312) | 4 => (-52489 / 16560) | 5 => (-1935469 / 612720) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | 1 => (-3841 / 324) | 2 => (-244609 / 20736) | 3 => (-129195409 / 10969344) | 4 => (-3227676121 / 274233600) | 5 => (-4417109024113 / 375425798400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C11T04_ok : C11T04.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T04_den : ℕ := 1
theorem C11T04_den_ok :
    (∀ d ∈ C11T04.R, ∀ e ∈ C11T04.R, (C11T04.Lq d e).den ∣ C11T04_den ∧ (C11T04.Lq' d e).den ∣ C11T04_den) ∧
    (∀ d ∈ C11T04.C, ∀ e ∈ C11T04.C, (C11T04.Pq d e).den ∣ C11T04_den ∧ (C11T04.Pq' d e).den ∣ C11T04_den) := by
  constructor <;> decide +kernel
#print axioms C11T04_ok
#print axioms C11T04_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
