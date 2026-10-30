import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 4f1ac512b9120b5e32a065dc5e3b90e91fee5b32a5a58685884d15bf1b703c2b, root class 1. -/
def C1T20 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7) | 1 => (-55 / 8) | 2 => (-821 / 120) | _ => 0
  ee := fun d => match d with | 0 => (-49) | 1 => (-3121 / 64) | 2 => (-701761 / 14400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T20_ok : C1T20.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T20_den : ℕ := 1
theorem C1T20_den_ok :
    (∀ d ∈ C1T20.R, ∀ e ∈ C1T20.R, (C1T20.Lq d e).den ∣ C1T20_den ∧ (C1T20.Lq' d e).den ∣ C1T20_den) ∧
    (∀ d ∈ C1T20.C, ∀ e ∈ C1T20.C, (C1T20.Pq d e).den ∣ C1T20_den ∧ (C1T20.Pq' d e).den ∣ C1T20_den) := by
  constructor <;> decide +kernel
#print axioms C1T20_ok
#print axioms C1T20_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
