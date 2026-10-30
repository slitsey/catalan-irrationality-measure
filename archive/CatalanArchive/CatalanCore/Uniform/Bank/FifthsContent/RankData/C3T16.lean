import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 93980c9c6b3e9a8d277cab15bfc29dbcea91f927fd6079053944093aa216aa1f, prime class 3 mod 10. -/
def C3T16 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5 / 2) | 1 => (-31 / 14) | 2 => (-179 / 84) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | 1 => (-1129 / 196) | 2 => (-40105 / 7056) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T16_ok : C3T16.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T16_den : ℕ := 1
theorem C3T16_den_ok :
    (∀ d ∈ C3T16.R, ∀ e ∈ C3T16.R, (C3T16.Lq d e).den ∣ C3T16_den ∧ (C3T16.Lq' d e).den ∣ C3T16_den) ∧
    (∀ d ∈ C3T16.C, ∀ e ∈ C3T16.C, (C3T16.Pq d e).den ∣ C3T16_den ∧ (C3T16.Pq' d e).den ∣ C3T16_den) := by
  constructor <;> decide +kernel
#print axioms C3T16_ok
#print axioms C3T16_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
