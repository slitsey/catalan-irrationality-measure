import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type cccd4ec0dccd80e6a04101c896aaa11b7089e5334f01d89c12b039b6267a051c, prime class 3 mod 10. -/
def C3T25 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T25_ok : C3T25.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T25_den : ℕ := 1
theorem C3T25_den_ok :
    (∀ d ∈ C3T25.R, ∀ e ∈ C3T25.R, (C3T25.Lq d e).den ∣ C3T25_den ∧ (C3T25.Lq' d e).den ∣ C3T25_den) ∧
    (∀ d ∈ C3T25.C, ∀ e ∈ C3T25.C, (C3T25.Pq d e).den ∣ C3T25_den ∧ (C3T25.Pq' d e).den ∣ C3T25_den) := by
  constructor <;> decide +kernel
#print axioms C3T25_ok
#print axioms C3T25_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
