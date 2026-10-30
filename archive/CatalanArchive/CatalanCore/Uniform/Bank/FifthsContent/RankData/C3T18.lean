import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 1376467842edce152bb2e67430f8704a22e5309abee9921bbdbfaf1a47187891, prime class 3 mod 10. -/
def C3T18 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5 / 2) | 1 => (-31 / 14) | 2 => (-179 / 84) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | 1 => (-1129 / 196) | 2 => (-40105 / 7056) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-11405 / 394254) | 1, 1 => 1 | 1, 2 => (-367 / 28161) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (11405 / 394254) | 1, 1 => 1 | 1, 2 => (367 / 28161) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C3T18_ok : C3T18.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T18_den : ℕ := 394254
theorem C3T18_den_ok :
    (∀ d ∈ C3T18.R, ∀ e ∈ C3T18.R, (C3T18.Lq d e).den ∣ C3T18_den ∧ (C3T18.Lq' d e).den ∣ C3T18_den) ∧
    (∀ d ∈ C3T18.C, ∀ e ∈ C3T18.C, (C3T18.Pq d e).den ∣ C3T18_den ∧ (C3T18.Pq' d e).den ∣ C3T18_den) := by
  constructor <;> decide +kernel
theorem C3T18_cload_2 : C3T18.cload 2 = ((377711 / 394254), (-38107 / 18774)) := by decide +kernel
#print axioms C3T18_ok
#print axioms C3T18_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
