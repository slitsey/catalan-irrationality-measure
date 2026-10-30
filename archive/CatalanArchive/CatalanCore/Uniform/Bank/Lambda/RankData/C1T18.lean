import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 57e0128e57908532eb34204367d1b49b2354a2db89b74749c224a2871f286299, root class 1. -/
def C1T18 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-4) | 1 => (-19 / 5) | 2 => (-337 / 90) | _ => 0
  ee := fun d => match d with | 0 => (-16) | 1 => (-391 / 25) | 2 => (-126259 / 8100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-2981 / 375300) | 1, 1 => 1 | 1, 2 => (-259 / 75060) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (2981 / 375300) | 1, 1 => 1 | 1, 2 => (259 / 75060) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C1T18_ok : C1T18.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T18_den : ℕ := 375300
theorem C1T18_den_ok :
    (∀ d ∈ C1T18.R, ∀ e ∈ C1T18.R, (C1T18.Lq d e).den ∣ C1T18_den ∧ (C1T18.Lq' d e).den ∣ C1T18_den) ∧
    (∀ d ∈ C1T18.C, ∀ e ∈ C1T18.C, (C1T18.Pq d e).den ∣ C1T18_den ∧ (C1T18.Pq' d e).den ∣ C1T18_den) := by
  constructor <;> decide +kernel
theorem C1T18_cload_2 : C1T18.cload 2 = ((92756 / 93825), (-92563 / 25020)) := by decide +kernel
#print axioms C1T18_ok
#print axioms C1T18_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
