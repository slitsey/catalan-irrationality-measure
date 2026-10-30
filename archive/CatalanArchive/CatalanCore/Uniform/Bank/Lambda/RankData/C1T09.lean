import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 43ba8b6ae1b6e0f07e187eec9e4d2548473d76f7ccc60a8811064adc8e9cec96, root class 1. -/
def C1T09 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-3) | 2 => (-33 / 10) | 3 => (-307 / 90) | 4 => (-8117 / 2340) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-15) | 2 => (-1539 / 100) | 3 => (-125359 / 8100) | 4 => (-84918859 / 5475600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-296526992938409 / 286425769726980) | 1, 1 => 1 | 1, 4 => (-14312187669733 / 71606442431745) | 2, 2 => 1 | 2, 4 => (-18895942550603 / 171855461836188) | 3, 3 => 1 | 3, 4 => (-80386248419 / 1060836184174) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (296526992938409 / 286425769726980) | 1, 1 => 1 | 1, 4 => (14312187669733 / 71606442431745) | 2, 2 => 1 | 2, 4 => (18895942550603 / 171855461836188) | 3, 3 => 1 | 3, 4 => (80386248419 / 1060836184174) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C1T09_ok : C1T09.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T09_den : ℕ := 859277309180940
theorem C1T09_den_ok :
    (∀ d ∈ C1T09.R, ∀ e ∈ C1T09.R, (C1T09.Lq d e).den ∣ C1T09_den ∧ (C1T09.Lq' d e).den ∣ C1T09_den) ∧
    (∀ d ∈ C1T09.C, ∀ e ∈ C1T09.C, (C1T09.Pq d e).den ∣ C1T09_den ∧ (C1T09.Pq' d e).den ∣ C1T09_den) := by
  constructor <;> decide +kernel
theorem C1T09_cload_4 : C1T09.cload 4 = ((-1923630295976 / 4570623985005), (-257538007361335 / 114570307890792)) := by decide +kernel
#print axioms C1T09_ok
#print axioms C1T09_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
