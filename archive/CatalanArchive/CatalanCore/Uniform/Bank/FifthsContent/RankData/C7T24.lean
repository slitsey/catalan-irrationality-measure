import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 145467879fc0622dc4f58397b2aa368a7b22d682c57835ab49e40ca3248c5aab, prime class 7 mod 10. -/
def C7T24 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C7T24_ok : C7T24.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T24_den : ℕ := 1
theorem C7T24_den_ok :
    (∀ d ∈ C7T24.R, ∀ e ∈ C7T24.R, (C7T24.Lq d e).den ∣ C7T24_den ∧ (C7T24.Lq' d e).den ∣ C7T24_den) ∧
    (∀ d ∈ C7T24.C, ∀ e ∈ C7T24.C, (C7T24.Pq d e).den ∣ C7T24_den ∧ (C7T24.Pq' d e).den ∣ C7T24_den) := by
  constructor <;> decide +kernel
theorem C7T24_cload_1 : C7T24.cload 1 = (1, 0) := by decide +kernel
#print axioms C7T24_ok
#print axioms C7T24_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
