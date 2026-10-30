import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type fed79bdf52c01b23e552471b584288afa099f4b184325b13b019369107547672, root class 3. -/
def C3T28 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => (-4 / 3) | _ => 0
  ee := fun d => match d with | 0 => (-16 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T28_ok : C3T28.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T28_den : ℕ := 1
theorem C3T28_den_ok :
    (∀ d ∈ C3T28.R, ∀ e ∈ C3T28.R, (C3T28.Lq d e).den ∣ C3T28_den ∧ (C3T28.Lq' d e).den ∣ C3T28_den) ∧
    (∀ d ∈ C3T28.C, ∀ e ∈ C3T28.C, (C3T28.Pq d e).den ∣ C3T28_den ∧ (C3T28.Pq' d e).den ∣ C3T28_den) := by
  constructor <;> decide +kernel
#print axioms C3T28_ok
#print axioms C3T28_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
