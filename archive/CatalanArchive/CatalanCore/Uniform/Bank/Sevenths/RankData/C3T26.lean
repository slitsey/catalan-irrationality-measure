import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c2f2a18a336a8908d2107232c0eb52142ca66999590b9415f7bd48b0290b1d8e, root class 3. -/
def C3T26 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 5) | 2 => (-29 / 60) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24 / 25) | 2 => (-3781 / 3600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-199 / 120) | 2, 1 => (-29 / 48) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (199 / 120) | 2, 1 => (29 / 48) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C3T26_ok : C3T26.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T26_den : ℕ := 240
theorem C3T26_den_ok :
    (∀ d ∈ C3T26.R, ∀ e ∈ C3T26.R, (C3T26.Lq d e).den ∣ C3T26_den ∧ (C3T26.Lq' d e).den ∣ C3T26_den) ∧
    (∀ d ∈ C3T26.C, ∀ e ∈ C3T26.C, (C3T26.Pq d e).den ∣ C3T26_den ∧ (C3T26.Pq' d e).den ∣ C3T26_den) := by
  constructor <;> decide +kernel
theorem C3T26_rload_2 : C3T26.rload 2 = ((-101 / 80), (-29 / 120)) := by decide +kernel
#print axioms C3T26_ok
#print axioms C3T26_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
