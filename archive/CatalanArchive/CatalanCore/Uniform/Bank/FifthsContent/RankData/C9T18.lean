import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 31454c9d39c31a50f1bcbab79c59ceb7b2c1c032925cfb4c811b29048f7d28fa, prime class 9 mod 10. -/
def C9T18 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | 2 => (-11 / 36) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | 2 => (-805 / 1296) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-115 / 72) | 1, 1 => 1 | 1, 2 => (-11 / 18) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (115 / 72) | 1, 1 => 1 | 1, 2 => (11 / 18) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C9T18_ok : C9T18.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T18_den : ℕ := 72
theorem C9T18_den_ok :
    (∀ d ∈ C9T18.R, ∀ e ∈ C9T18.R, (C9T18.Lq d e).den ∣ C9T18_den ∧ (C9T18.Lq' d e).den ∣ C9T18_den) ∧
    (∀ d ∈ C9T18.C, ∀ e ∈ C9T18.C, (C9T18.Pq d e).den ∣ C9T18_den ∧ (C9T18.Pq' d e).den ∣ C9T18_den) := by
  constructor <;> decide +kernel
theorem C9T18_cload_2 : C9T18.cload 2 = ((-29 / 24), (-11 / 72)) := by decide +kernel
#print axioms C9T18_ok
#print axioms C9T18_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
