import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type bf71d7b608bb4b42a17e0658ecb97f383ece1325bd6c7da4d4ae869dcbb9cd56, root class 3. -/
def C3T14 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 3) | 2 => (-17 / 42) | 3 => (-67 / 154) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-7 / 9) | 2 => (-1507 / 1764) | 3 => (-62285 / 71148) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-3413083 / 4002306) | 1, 1 => 1 | 1, 3 => (-847991 / 2668204) | 2, 2 => 1 | 2, 3 => (-1673 / 8663) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (3413083 / 4002306) | 1, 1 => 1 | 1, 3 => (847991 / 2668204) | 2, 2 => 1 | 2, 3 => (1673 / 8663) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C3T14_ok : C3T14.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T14_den : ℕ := 8004612
theorem C3T14_den_ok :
    (∀ d ∈ C3T14.R, ∀ e ∈ C3T14.R, (C3T14.Lq d e).den ∣ C3T14_den ∧ (C3T14.Lq' d e).den ∣ C3T14_den) ∧
    (∀ d ∈ C3T14.C, ∀ e ∈ C3T14.C, (C3T14.Pq d e).den ∣ C3T14_den ∧ (C3T14.Pq' d e).den ∣ C3T14_den) := by
  constructor <;> decide +kernel
theorem C3T14_cload_3 : C3T14.cload 3 = ((-2911379 / 8004612), (-669611 / 2668204)) := by decide +kernel
#print axioms C3T14_ok
#print axioms C3T14_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
