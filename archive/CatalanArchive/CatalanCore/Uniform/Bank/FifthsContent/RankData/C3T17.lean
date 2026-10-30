import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 1a612dd4e8b5ac941ca845958a403015f0c35033e361f14c8313c2752190132b, prime class 3 mod 10. -/
def C3T17 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-5 / 2) | 1 => (-31 / 14) | 2 => (-179 / 84) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | 1 => (-1129 / 196) | 2 => (-40105 / 7056) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-11405 / 394254) | 2, 1 => (-367 / 28161) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (11405 / 394254) | 2, 1 => (367 / 28161) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C3T17_ok : C3T17.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T17_den : ℕ := 394254
theorem C3T17_den_ok :
    (∀ d ∈ C3T17.R, ∀ e ∈ C3T17.R, (C3T17.Lq d e).den ∣ C3T17_den ∧ (C3T17.Lq' d e).den ∣ C3T17_den) ∧
    (∀ d ∈ C3T17.C, ∀ e ∈ C3T17.C, (C3T17.Pq d e).den ∣ C3T17_den ∧ (C3T17.Pq' d e).den ∣ C3T17_den) := by
  constructor <;> decide +kernel
theorem C3T17_rload_2 : C3T17.rload 2 = ((377711 / 394254), (-38107 / 18774)) := by decide +kernel
#print axioms C3T17_ok
#print axioms C3T17_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
