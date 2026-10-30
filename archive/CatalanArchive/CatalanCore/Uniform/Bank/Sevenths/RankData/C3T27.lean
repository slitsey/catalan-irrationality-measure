import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 33114ac6ac70795623de41cf2d65f9199956d284bc853cdee677b7485d310570, root class 3. -/
def C3T27 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 5) | 2 => (-29 / 60) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24 / 25) | 2 => (-3781 / 3600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-199 / 120) | 1, 1 => 1 | 1, 2 => (-29 / 48) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (199 / 120) | 1, 1 => 1 | 1, 2 => (29 / 48) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C3T27_ok : C3T27.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T27_den : ℕ := 240
theorem C3T27_den_ok :
    (∀ d ∈ C3T27.R, ∀ e ∈ C3T27.R, (C3T27.Lq d e).den ∣ C3T27_den ∧ (C3T27.Lq' d e).den ∣ C3T27_den) ∧
    (∀ d ∈ C3T27.C, ∀ e ∈ C3T27.C, (C3T27.Pq d e).den ∣ C3T27_den ∧ (C3T27.Pq' d e).den ∣ C3T27_den) := by
  constructor <;> decide +kernel
theorem C3T27_cload_2 : C3T27.cload 2 = ((-101 / 80), (-29 / 120)) := by decide +kernel
#print axioms C3T27_ok
#print axioms C3T27_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
