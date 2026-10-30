import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type a966d01bd5ad6d16c0c4e3cf87013e8033a45a684455b774ddd9b63f4358ac73, prime class 7 mod 10. -/
def C7T19 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-5 / 3) | 1 => (-31 / 24) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | 1 => (-1249 / 576) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C7T19_ok : C7T19.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T19_den : ℕ := 1
theorem C7T19_den_ok :
    (∀ d ∈ C7T19.R, ∀ e ∈ C7T19.R, (C7T19.Lq d e).den ∣ C7T19_den ∧ (C7T19.Lq' d e).den ∣ C7T19_den) ∧
    (∀ d ∈ C7T19.C, ∀ e ∈ C7T19.C, (C7T19.Pq d e).den ∣ C7T19_den ∧ (C7T19.Pq' d e).den ∣ C7T19_den) := by
  constructor <;> decide +kernel
#print axioms C7T19_ok
#print axioms C7T19_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
