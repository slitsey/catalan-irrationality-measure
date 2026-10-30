import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d0fcd94fb3edafb6118dc96a9f70725bb074e867eefb74023a9d3bfa8a214b0a, root class 3. -/
def C3T24 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-4 / 3) | 1 => (-19 / 21) | _ => 0
  ee := fun d => match d with | 0 => (-16 / 9) | 1 => (-487 / 441) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (-27 / 112) | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (27 / 112) | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C3T24_ok : C3T24.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T24_den : ℕ := 112
theorem C3T24_den_ok :
    (∀ d ∈ C3T24.R, ∀ e ∈ C3T24.R, (C3T24.Lq d e).den ∣ C3T24_den ∧ (C3T24.Lq' d e).den ∣ C3T24_den) ∧
    (∀ d ∈ C3T24.C, ∀ e ∈ C3T24.C, (C3T24.Pq d e).den ∣ C3T24_den ∧ (C3T24.Pq' d e).den ∣ C3T24_den) := by
  constructor <;> decide +kernel
theorem C3T24_cload_1 : C3T24.cload 1 = ((85 / 112), (-7 / 12)) := by decide +kernel
#print axioms C3T24_ok
#print axioms C3T24_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
