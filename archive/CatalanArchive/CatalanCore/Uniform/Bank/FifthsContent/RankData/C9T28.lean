import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type b0dfe0943e1c06d1ba62ed1cb8f9e4717da87ea4e3ff6e3f92f7218fe671e9c0, prime class 9 mod 10. -/
def C9T28 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => (-5 / 4) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C9T28_ok : C9T28.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T28_den : ℕ := 1
theorem C9T28_den_ok :
    (∀ d ∈ C9T28.R, ∀ e ∈ C9T28.R, (C9T28.Lq d e).den ∣ C9T28_den ∧ (C9T28.Lq' d e).den ∣ C9T28_den) ∧
    (∀ d ∈ C9T28.C, ∀ e ∈ C9T28.C, (C9T28.Pq d e).den ∣ C9T28_den ∧ (C9T28.Pq' d e).den ∣ C9T28_den) := by
  constructor <;> decide +kernel
theorem C9T28_cload_0 : C9T28.cload 0 = (1, (-5 / 4)) := by decide +kernel
#print axioms C9T28_ok
#print axioms C9T28_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
