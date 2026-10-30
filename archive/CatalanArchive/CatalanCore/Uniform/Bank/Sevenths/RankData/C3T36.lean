import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c10eaf15dcad039d64a8534f0c0b81763235b7a391667efb11f4f47ef043117e, root class 3. -/
def C3T36 : FibreCert where
  R := {0}
  C := ∅
  lf := fun d => match d with | 0 => (-7 / 5) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun _ _ => 0
  Pq' := fun _ _ => 0
  kr := {0}
  kc := ∅

theorem C3T36_ok : C3T36.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T36_den : ℕ := 1
theorem C3T36_den_ok :
    (∀ d ∈ C3T36.R, ∀ e ∈ C3T36.R, (C3T36.Lq d e).den ∣ C3T36_den ∧ (C3T36.Lq' d e).den ∣ C3T36_den) ∧
    (∀ d ∈ C3T36.C, ∀ e ∈ C3T36.C, (C3T36.Pq d e).den ∣ C3T36_den ∧ (C3T36.Pq' d e).den ∣ C3T36_den) := by
  constructor <;> decide +kernel
theorem C3T36_rload_0 : C3T36.rload 0 = (1, (-7 / 5)) := by decide +kernel
#print axioms C3T36_ok
#print axioms C3T36_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
