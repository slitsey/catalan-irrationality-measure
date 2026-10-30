import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type b06a551c6dfeeb58e619bf9f215dd5b450aa968fe3fb05797dfbac83f6663901, prime class 3 mod 10. -/
def C3T24 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => (-5 / 2) | 1 => (-31 / 14) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | 1 => (-1129 / 196) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (-8 / 175) | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (8 / 175) | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C3T24_ok : C3T24.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T24_den : ℕ := 175
theorem C3T24_den_ok :
    (∀ d ∈ C3T24.R, ∀ e ∈ C3T24.R, (C3T24.Lq d e).den ∣ C3T24_den ∧ (C3T24.Lq' d e).den ∣ C3T24_den) ∧
    (∀ d ∈ C3T24.C, ∀ e ∈ C3T24.C, (C3T24.Pq d e).den ∣ C3T24_den ∧ (C3T24.Pq' d e).den ∣ C3T24_den) := by
  constructor <;> decide +kernel
theorem C3T24_rload_1 : C3T24.rload 1 = ((167 / 175), (-21 / 10)) := by decide +kernel
#print axioms C3T24_ok
#print axioms C3T24_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
