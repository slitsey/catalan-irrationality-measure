import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type f38ec5e42b2760c7464ab17da97013defd04f18acd24bfda50789e7298e58611, root class 3. -/
def C3T37 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 5) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C3T37_ok : C3T37.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T37_den : ℕ := 1
theorem C3T37_den_ok :
    (∀ d ∈ C3T37.R, ∀ e ∈ C3T37.R, (C3T37.Lq d e).den ∣ C3T37_den ∧ (C3T37.Lq' d e).den ∣ C3T37_den) ∧
    (∀ d ∈ C3T37.C, ∀ e ∈ C3T37.C, (C3T37.Pq d e).den ∣ C3T37_den ∧ (C3T37.Pq' d e).den ∣ C3T37_den) := by
  constructor <;> decide +kernel
theorem C3T37_cload_0 : C3T37.cload 0 = (1, (-7 / 5)) := by decide +kernel
#print axioms C3T37_ok
#print axioms C3T37_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
