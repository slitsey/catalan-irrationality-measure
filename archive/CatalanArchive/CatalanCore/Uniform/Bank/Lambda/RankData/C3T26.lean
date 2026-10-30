import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 8e36aef2e69afb6e58576e90df965f6e263c4c758bba700cdb99d65adbca7096, root class 3. -/
def C3T26 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-7 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C3T26_ok : C3T26.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T26_den : ℕ := 1
theorem C3T26_den_ok :
    (∀ d ∈ C3T26.R, ∀ e ∈ C3T26.R, (C3T26.Lq d e).den ∣ C3T26_den ∧ (C3T26.Lq' d e).den ∣ C3T26_den) ∧
    (∀ d ∈ C3T26.C, ∀ e ∈ C3T26.C, (C3T26.Pq d e).den ∣ C3T26_den ∧ (C3T26.Pq' d e).den ∣ C3T26_den) := by
  constructor <;> decide +kernel
theorem C3T26_cload_1 : C3T26.cload 1 = (1, 0) := by decide +kernel
#print axioms C3T26_ok
#print axioms C3T26_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
