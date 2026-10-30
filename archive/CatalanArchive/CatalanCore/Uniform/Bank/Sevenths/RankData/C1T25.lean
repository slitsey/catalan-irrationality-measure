import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d9a6bea135fdc95c75dfef4d2d4af15531acdd79ef1020f3b7907dc283e4dbac, root class 1. -/
def C1T25 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | 2 => (-51 / 8) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | 2 => (-3105 / 64) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T25_ok : C1T25.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T25_den : ℕ := 1
theorem C1T25_den_ok :
    (∀ d ∈ C1T25.R, ∀ e ∈ C1T25.R, (C1T25.Lq d e).den ∣ C1T25_den ∧ (C1T25.Lq' d e).den ∣ C1T25_den) ∧
    (∀ d ∈ C1T25.C, ∀ e ∈ C1T25.C, (C1T25.Pq d e).den ∣ C1T25_den ∧ (C1T25.Pq' d e).den ∣ C1T25_den) := by
  constructor <;> decide +kernel
#print axioms C1T25_ok
#print axioms C1T25_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
