import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 8343442daa18be1e25ef28f56eb5392a11cabcf006eb2798f2b09bff5ae7bd01, prime class 3 mod 10. -/
def C3T10 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-5 / 2) | 1 => (-31 / 14) | 2 => (-179 / 84) | 3 => (-2987 / 1428) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | 1 => (-1129 / 196) | 2 => (-40105 / 7056) | 3 => (-1282241 / 226576) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T10_ok : C3T10.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T10_den : ℕ := 1
theorem C3T10_den_ok :
    (∀ d ∈ C3T10.R, ∀ e ∈ C3T10.R, (C3T10.Lq d e).den ∣ C3T10_den ∧ (C3T10.Lq' d e).den ∣ C3T10_den) ∧
    (∀ d ∈ C3T10.C, ∀ e ∈ C3T10.C, (C3T10.Pq d e).den ∣ C3T10_den ∧ (C3T10.Pq' d e).den ∣ C3T10_den) := by
  constructor <;> decide +kernel
#print axioms C3T10_ok
#print axioms C3T10_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
