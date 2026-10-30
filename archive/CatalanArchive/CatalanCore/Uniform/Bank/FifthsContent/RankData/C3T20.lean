import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type cfe2b67f2511972412485405f4bceb74a43cb46e780d9a2993b455e93942bf5a, prime class 3 mod 10. -/
def C3T20 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-5 / 2) | 1 => (-31 / 14) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | 1 => (-1129 / 196) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T20_ok : C3T20.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T20_den : ℕ := 1
theorem C3T20_den_ok :
    (∀ d ∈ C3T20.R, ∀ e ∈ C3T20.R, (C3T20.Lq d e).den ∣ C3T20_den ∧ (C3T20.Lq' d e).den ∣ C3T20_den) ∧
    (∀ d ∈ C3T20.C, ∀ e ∈ C3T20.C, (C3T20.Pq d e).den ∣ C3T20_den ∧ (C3T20.Pq' d e).den ∣ C3T20_den) := by
  constructor <;> decide +kernel
#print axioms C3T20_ok
#print axioms C3T20_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
