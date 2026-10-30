import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type c316a1daf254becf377bec38cf4d922fe5a7e35569880d507f93fecba9d3d706, prime class 9 mod 10. -/
def C9T21 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-5 / 4) | 1 => (-29 / 36) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | 1 => (-1129 / 1296) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (-64 / 225) | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (64 / 225) | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C9T21_ok : C9T21.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T21_den : ℕ := 225
theorem C9T21_den_ok :
    (∀ d ∈ C9T21.R, ∀ e ∈ C9T21.R, (C9T21.Lq d e).den ∣ C9T21_den ∧ (C9T21.Lq' d e).den ∣ C9T21_den) ∧
    (∀ d ∈ C9T21.C, ∀ e ∈ C9T21.C, (C9T21.Pq d e).den ∣ C9T21_den ∧ (C9T21.Pq' d e).den ∣ C9T21_den) := by
  constructor <;> decide +kernel
theorem C9T21_cload_1 : C9T21.cload 1 = ((161 / 225), (-9 / 20)) := by decide +kernel
#print axioms C9T21_ok
#print axioms C9T21_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
