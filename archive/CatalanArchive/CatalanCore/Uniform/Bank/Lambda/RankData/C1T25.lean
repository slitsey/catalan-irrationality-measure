import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 1abcd469f31a17d26292386d676701460e5daffa54a431d439b9718d3b5e4ef9, root class 1. -/
def C1T25 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-15) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
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
end CatalanCore.Uniform.Bank.Lambda.RankData
