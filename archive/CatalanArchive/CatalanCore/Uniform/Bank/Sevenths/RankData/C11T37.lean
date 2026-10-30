import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 8c59edc65d24ab53a036cadff8c5f1604bab737c95074cb3060647ed5b2aa995, root class 11. -/
def C11T37 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 2) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C11T37_ok : C11T37.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T37_den : ℕ := 1
theorem C11T37_den_ok :
    (∀ d ∈ C11T37.R, ∀ e ∈ C11T37.R, (C11T37.Lq d e).den ∣ C11T37_den ∧ (C11T37.Lq' d e).den ∣ C11T37_den) ∧
    (∀ d ∈ C11T37.C, ∀ e ∈ C11T37.C, (C11T37.Pq d e).den ∣ C11T37_den ∧ (C11T37.Pq' d e).den ∣ C11T37_den) := by
  constructor <;> decide +kernel
theorem C11T37_cload_0 : C11T37.cload 0 = (1, (-7 / 2)) := by decide +kernel
#print axioms C11T37_ok
#print axioms C11T37_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
