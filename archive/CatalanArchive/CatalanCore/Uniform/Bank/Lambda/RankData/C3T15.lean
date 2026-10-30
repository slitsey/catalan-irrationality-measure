import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d89466ecad4382983fd9dc8e9ab382aeb61418f4a636bd4a1981607242c0ee92, root class 3. -/
def C3T15 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 3) | 2 => (-17 / 42) | 3 => (-67 / 154) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-7 / 9) | 2 => (-1507 / 1764) | 3 => (-62285 / 71148) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-3413083 / 4002306) | 3, 1 => (-847991 / 2668204) | 3, 2 => (-1673 / 8663) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (3413083 / 4002306) | 3, 1 => (847991 / 2668204) | 3, 2 => (1673 / 8663) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C3T15_ok : C3T15.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T15_den : ℕ := 8004612
theorem C3T15_den_ok :
    (∀ d ∈ C3T15.R, ∀ e ∈ C3T15.R, (C3T15.Lq d e).den ∣ C3T15_den ∧ (C3T15.Lq' d e).den ∣ C3T15_den) ∧
    (∀ d ∈ C3T15.C, ∀ e ∈ C3T15.C, (C3T15.Pq d e).den ∣ C3T15_den ∧ (C3T15.Pq' d e).den ∣ C3T15_den) := by
  constructor <;> decide +kernel
theorem C3T15_rload_3 : C3T15.rload 3 = ((-2911379 / 8004612), (-669611 / 2668204)) := by decide +kernel
#print axioms C3T15_ok
#print axioms C3T15_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
