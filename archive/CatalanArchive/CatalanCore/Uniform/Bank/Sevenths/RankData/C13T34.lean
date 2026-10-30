import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 1a1b23f75cfb5dcbfed343b89c516928c37d736e2e1aaa7969d9064de63af551, root class 13. -/
def C13T34 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 6) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C13T34_ok : C13T34.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T34_den : ℕ := 1
theorem C13T34_den_ok :
    (∀ d ∈ C13T34.R, ∀ e ∈ C13T34.R, (C13T34.Lq d e).den ∣ C13T34_den ∧ (C13T34.Lq' d e).den ∣ C13T34_den) ∧
    (∀ d ∈ C13T34.C, ∀ e ∈ C13T34.C, (C13T34.Pq d e).den ∣ C13T34_den ∧ (C13T34.Pq' d e).den ∣ C13T34_den) := by
  constructor <;> decide +kernel
#print axioms C13T34_ok
#print axioms C13T34_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
