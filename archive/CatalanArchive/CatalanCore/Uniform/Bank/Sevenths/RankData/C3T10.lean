import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type f3ace0bba8b9180b98fb3a919d19a9d9da1292626cb30867136558e9137ee7a3, root class 3. -/
def C3T10 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-7 / 5) | 1 => (-59 / 60) | 2 => (-971 / 1140) | 3 => (-3891 / 4940) | 4 => (-30557 / 40755) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | 1 => (-4681 / 3600) | 2 => (-1541341 / 1299600) | 3 => (-84001043 / 73210800) | 4 => (-3753398123 / 3321940050) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T10_ok : C3T10.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T10_den : ℕ := 1
theorem C3T10_den_ok :
    (∀ d ∈ C3T10.R, ∀ e ∈ C3T10.R, (C3T10.Lq d e).den ∣ C3T10_den ∧ (C3T10.Lq' d e).den ∣ C3T10_den) ∧
    (∀ d ∈ C3T10.C, ∀ e ∈ C3T10.C, (C3T10.Pq d e).den ∣ C3T10_den ∧ (C3T10.Pq' d e).den ∣ C3T10_den) := by
  constructor <;> decide +kernel
#print axioms C3T10_ok
#print axioms C3T10_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
