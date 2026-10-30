import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 8c020facf129c367477c97ba2c10eff845a58eb2c5f851c56898c0efd79d87cf, root class 13. -/
def C13T23 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | 2 => (-8 / 39) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | 2 => (-610 / 1521) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C13T23_ok : C13T23.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T23_den : ℕ := 1
theorem C13T23_den_ok :
    (∀ d ∈ C13T23.R, ∀ e ∈ C13T23.R, (C13T23.Lq d e).den ∣ C13T23_den ∧ (C13T23.Lq' d e).den ∣ C13T23_den) ∧
    (∀ d ∈ C13T23.C, ∀ e ∈ C13T23.C, (C13T23.Pq d e).den ∣ C13T23_den ∧ (C13T23.Pq' d e).den ∣ C13T23_den) := by
  constructor <;> decide +kernel
#print axioms C13T23_ok
#print axioms C13T23_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
