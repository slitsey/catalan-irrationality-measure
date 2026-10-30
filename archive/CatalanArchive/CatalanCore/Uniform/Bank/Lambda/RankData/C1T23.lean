import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 4872ce0c56dbac20a9d34dbc56c0b53a233cf4638e3e78709880691b08c6fb22, root class 1. -/
def C1T23 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-4) | 1 => (-19 / 5) | _ => 0
  ee := fun d => match d with | 0 => (-16) | 1 => (-391 / 25) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (-1 / 80) | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (1 / 80) | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C1T23_ok : C1T23.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T23_den : ℕ := 80
theorem C1T23_den_ok :
    (∀ d ∈ C1T23.R, ∀ e ∈ C1T23.R, (C1T23.Lq d e).den ∣ C1T23_den ∧ (C1T23.Lq' d e).den ∣ C1T23_den) ∧
    (∀ d ∈ C1T23.C, ∀ e ∈ C1T23.C, (C1T23.Pq d e).den ∣ C1T23_den ∧ (C1T23.Pq' d e).den ∣ C1T23_den) := by
  constructor <;> decide +kernel
theorem C1T23_cload_1 : C1T23.cload 1 = ((79 / 80), (-15 / 4)) := by decide +kernel
#print axioms C1T23_ok
#print axioms C1T23_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
