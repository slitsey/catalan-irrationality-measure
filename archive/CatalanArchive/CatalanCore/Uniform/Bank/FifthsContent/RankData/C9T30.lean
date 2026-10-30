import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type f6665cde794ce2658d92a1963460a2c889e3eb270fc93e996e0d9a2ce65ee6a7, prime class 9 mod 10. -/
def C9T30 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => 0 | _ => 0
  ee := fun d => match d with | 0 => 0 | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C9T30_ok : C9T30.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T30_den : ℕ := 1
theorem C9T30_den_ok :
    (∀ d ∈ C9T30.R, ∀ e ∈ C9T30.R, (C9T30.Lq d e).den ∣ C9T30_den ∧ (C9T30.Lq' d e).den ∣ C9T30_den) ∧
    (∀ d ∈ C9T30.C, ∀ e ∈ C9T30.C, (C9T30.Pq d e).den ∣ C9T30_den ∧ (C9T30.Pq' d e).den ∣ C9T30_den) := by
  constructor <;> decide +kernel
theorem C9T30_cload_0 : C9T30.cload 0 = (1, 0) := by decide +kernel
#print axioms C9T30_ok
#print axioms C9T30_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
