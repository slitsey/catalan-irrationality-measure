import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 0f081efc88d30a91661f97110ae1740f510226f4bd8fa0b1783b5e415431a8b2, prime class 3 mod 10. -/
def C3T31 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => (-5 / 2) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C3T31_ok : C3T31.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T31_den : ℕ := 1
theorem C3T31_den_ok :
    (∀ d ∈ C3T31.R, ∀ e ∈ C3T31.R, (C3T31.Lq d e).den ∣ C3T31_den ∧ (C3T31.Lq' d e).den ∣ C3T31_den) ∧
    (∀ d ∈ C3T31.C, ∀ e ∈ C3T31.C, (C3T31.Pq d e).den ∣ C3T31_den ∧ (C3T31.Pq' d e).den ∣ C3T31_den) := by
  constructor <;> decide +kernel
theorem C3T31_cload_0 : C3T31.cload 0 = (1, (-5 / 2)) := by decide +kernel
#print axioms C3T31_ok
#print axioms C3T31_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
