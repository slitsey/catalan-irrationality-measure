import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type b206460b30bf966248f8bbde703bce5eb99550448b554bdfac7d4ee738d3ceeb, prime class 9 mod 10. -/
def C9T25 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => (-5 / 4) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T25_ok : C9T25.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T25_den : ℕ := 1
theorem C9T25_den_ok :
    (∀ d ∈ C9T25.R, ∀ e ∈ C9T25.R, (C9T25.Lq d e).den ∣ C9T25_den ∧ (C9T25.Lq' d e).den ∣ C9T25_den) ∧
    (∀ d ∈ C9T25.C, ∀ e ∈ C9T25.C, (C9T25.Pq d e).den ∣ C9T25_den ∧ (C9T25.Pq' d e).den ∣ C9T25_den) := by
  constructor <;> decide +kernel
#print axioms C9T25_ok
#print axioms C9T25_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
