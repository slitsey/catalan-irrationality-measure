import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type e50021fa9c58a6cc34c99641a8ba98a876659c2bdf88cf25e09941d11257b034, root class 1. -/
def C1T04 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => (-7) | 1 => (-55 / 8) | 2 => (-821 / 120) | 3 => (-9011 / 1320) | 4 => (-260989 / 38280) | 5 => (-782329 / 114840) | _ => 0
  ee := fun d => match d with | 0 => (-49) | 1 => (-3121 / 64) | 2 => (-701761 / 14400) | 3 => (-28298627 / 580800) | 4 => (-23797076207 / 488452800) | 5 => (-128498431493 / 2637645120) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
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
end CatalanCore.Uniform.Bank.Sevenths.RankData
