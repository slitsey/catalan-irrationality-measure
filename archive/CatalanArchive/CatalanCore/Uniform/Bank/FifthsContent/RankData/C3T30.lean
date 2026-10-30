import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 3b541e205dc9fadf54cb092ad122da974392f5f56733668cc81b3e636c9ce496, prime class 3 mod 10. -/
def C3T30 : FibreCert where
  R := {0}
  C := ∅
  lf := fun d => match d with | 0 => (-5 / 2) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun _ _ => 0
  Pq' := fun _ _ => 0
  kr := {0}
  kc := ∅

theorem C3T30_ok : C3T30.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T30_den : ℕ := 1
theorem C3T30_den_ok :
    (∀ d ∈ C3T30.R, ∀ e ∈ C3T30.R, (C3T30.Lq d e).den ∣ C3T30_den ∧ (C3T30.Lq' d e).den ∣ C3T30_den) ∧
    (∀ d ∈ C3T30.C, ∀ e ∈ C3T30.C, (C3T30.Pq d e).den ∣ C3T30_den ∧ (C3T30.Pq' d e).den ∣ C3T30_den) := by
  constructor <;> decide +kernel
theorem C3T30_rload_0 : C3T30.rload 0 = (1, (-5 / 2)) := by decide +kernel
#print axioms C3T30_ok
#print axioms C3T30_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
