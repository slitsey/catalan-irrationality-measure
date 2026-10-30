import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 57d187874ee43bf83ba78c00eaac31ed845b3dab8dfc32a666db579c1476ed1a, root class 3. -/
def C3T04 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => (-7 / 5) | 1 => (-59 / 60) | 2 => (-971 / 1140) | 3 => (-3891 / 4940) | 4 => (-30557 / 40755) | 5 => (-47261 / 65208) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | 1 => (-4681 / 3600) | 2 => (-1541341 / 1299600) | 3 => (-84001043 / 73210800) | 4 => (-3753398123 / 3321940050) | 5 => (-119112157921 / 106302081600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T04_ok : C3T04.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T04_den : ℕ := 1
theorem C3T04_den_ok :
    (∀ d ∈ C3T04.R, ∀ e ∈ C3T04.R, (C3T04.Lq d e).den ∣ C3T04_den ∧ (C3T04.Lq' d e).den ∣ C3T04_den) ∧
    (∀ d ∈ C3T04.C, ∀ e ∈ C3T04.C, (C3T04.Pq d e).den ∣ C3T04_den ∧ (C3T04.Pq' d e).den ∣ C3T04_den) := by
  constructor <;> decide +kernel
#print axioms C3T04_ok
#print axioms C3T04_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
