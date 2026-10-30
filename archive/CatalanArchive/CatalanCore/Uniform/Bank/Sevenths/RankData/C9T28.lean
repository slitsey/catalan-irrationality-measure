import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 18d0d0b68f20dcf586436c762d46dd7d00f81e9ed061add01322364478dbd33a, root class 9. -/
def C9T28 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T28_ok : C9T28.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T28_den : ℕ := 1
theorem C9T28_den_ok :
    (∀ d ∈ C9T28.R, ∀ e ∈ C9T28.R, (C9T28.Lq d e).den ∣ C9T28_den ∧ (C9T28.Lq' d e).den ∣ C9T28_den) ∧
    (∀ d ∈ C9T28.C, ∀ e ∈ C9T28.C, (C9T28.Pq d e).den ∣ C9T28_den ∧ (C9T28.Pq' d e).den ∣ C9T28_den) := by
  constructor <;> decide +kernel
#print axioms C9T28_ok
#print axioms C9T28_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
