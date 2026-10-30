import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d6e97422e96a4748c965d30e1a7d9b5077d328ecd9f83a278782b3e4001fb43a, root class 1. -/
def C1T30 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => (-7) | 1 => (-55 / 8) | _ => 0
  ee := fun d => match d with | 0 => (-49) | 1 => (-3121 / 64) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (-1 / 392) | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (1 / 392) | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C1T30_ok : C1T30.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T30_den : ℕ := 392
theorem C1T30_den_ok :
    (∀ d ∈ C1T30.R, ∀ e ∈ C1T30.R, (C1T30.Lq d e).den ∣ C1T30_den ∧ (C1T30.Lq' d e).den ∣ C1T30_den) ∧
    (∀ d ∈ C1T30.C, ∀ e ∈ C1T30.C, (C1T30.Pq d e).den ∣ C1T30_den ∧ (C1T30.Pq' d e).den ∣ C1T30_den) := by
  constructor <;> decide +kernel
theorem C1T30_rload_1 : C1T30.rload 1 = ((391 / 392), (-48 / 7)) := by decide +kernel
#print axioms C1T30_ok
#print axioms C1T30_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
