import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type f6665cde794ce2658d92a1963460a2c889e3eb270fc93e996e0d9a2ce65ee6a7, prime class 1 mod 10. -/
def C1T33 : FibreCert where
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

theorem C1T33_ok : C1T33.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T33_den : ℕ := 1
theorem C1T33_den_ok :
    (∀ d ∈ C1T33.R, ∀ e ∈ C1T33.R, (C1T33.Lq d e).den ∣ C1T33_den ∧ (C1T33.Lq' d e).den ∣ C1T33_den) ∧
    (∀ d ∈ C1T33.C, ∀ e ∈ C1T33.C, (C1T33.Pq d e).den ∣ C1T33_den ∧ (C1T33.Pq' d e).den ∣ C1T33_den) := by
  constructor <;> decide +kernel
theorem C1T33_cload_0 : C1T33.cload 0 = (1, 0) := by decide +kernel
#print axioms C1T33_ok
#print axioms C1T33_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
