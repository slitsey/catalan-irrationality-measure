import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 94f9cf393183335140dd0b4a8261c62f071e694404dc5ff7bd465bde7d1b873b, prime class 3 mod 10. -/
def C3T12 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5 / 2) | 1 => (-31 / 14) | 2 => (-179 / 84) | 3 => (-2987 / 1428) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | 1 => (-1129 / 196) | 2 => (-40105 / 7056) | 3 => (-1282241 / 226576) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-2130534199 / 100684749627) | 3, 1 => (-273290287 / 28767071322) | 3, 2 => (-1712848 / 282030111) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (2130534199 / 100684749627) | 3, 1 => (273290287 / 28767071322) | 3, 2 => (1712848 / 282030111) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C3T12_ok : C3T12.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T12_den : ℕ := 201369499254
theorem C3T12_den_ok :
    (∀ d ∈ C3T12.R, ∀ e ∈ C3T12.R, (C3T12.Lq d e).den ∣ C3T12_den ∧ (C3T12.Lq' d e).den ∣ C3T12_den) ∧
    (∀ d ∈ C3T12.C, ∀ e ∈ C3T12.C, (C3T12.Pq d e).den ∣ C3T12_den ∧ (C3T12.Pq' d e).den ∣ C3T12_den) := by
  constructor <;> decide +kernel
theorem C3T12_rload_3 : C3T12.rload 3 = ((64657475125 / 67123166418), (-134572400701 / 67123166418)) := by decide +kernel
#print axioms C3T12_ok
#print axioms C3T12_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
