import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 553ed348a9a9a5cb17dabfd8150f90cdd59fce475219ba08fd3937c85548c393, root class 1. -/
def C1T27 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-15) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C1T27_ok : C1T27.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T27_den : ℕ := 1
theorem C1T27_den_ok :
    (∀ d ∈ C1T27.R, ∀ e ∈ C1T27.R, (C1T27.Lq d e).den ∣ C1T27_den ∧ (C1T27.Lq' d e).den ∣ C1T27_den) ∧
    (∀ d ∈ C1T27.C, ∀ e ∈ C1T27.C, (C1T27.Pq d e).den ∣ C1T27_den ∧ (C1T27.Pq' d e).den ∣ C1T27_den) := by
  constructor <;> decide +kernel
theorem C1T27_cload_1 : C1T27.cload 1 = (1, 0) := by decide +kernel
#print axioms C1T27_ok
#print axioms C1T27_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
