import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type f7445445266439e17e7d72a94f4cc3f382659b7bad9b1dbfea80fc4a1f6b40d9, root class 13. -/
def C13T28 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 6) | 1 => (-55 / 78) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | 1 => (-3961 / 6084) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C13T28_ok : C13T28.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T28_den : ℕ := 1
theorem C13T28_den_ok :
    (∀ d ∈ C13T28.R, ∀ e ∈ C13T28.R, (C13T28.Lq d e).den ∣ C13T28_den ∧ (C13T28.Lq' d e).den ∣ C13T28_den) ∧
    (∀ d ∈ C13T28.C, ∀ e ∈ C13T28.C, (C13T28.Pq d e).den ∣ C13T28_den ∧ (C13T28.Pq' d e).den ∣ C13T28_den) := by
  constructor <;> decide +kernel
#print axioms C13T28_ok
#print axioms C13T28_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
