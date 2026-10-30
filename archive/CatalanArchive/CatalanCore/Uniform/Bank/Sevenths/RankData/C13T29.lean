import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type ef575668a29860117c605f1545ed754f139721be295b27d3683642062141466f, root class 13. -/
def C13T29 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C13T29_ok : C13T29.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T29_den : ℕ := 1
theorem C13T29_den_ok :
    (∀ d ∈ C13T29.R, ∀ e ∈ C13T29.R, (C13T29.Lq d e).den ∣ C13T29_den ∧ (C13T29.Lq' d e).den ∣ C13T29_den) ∧
    (∀ d ∈ C13T29.C, ∀ e ∈ C13T29.C, (C13T29.Pq d e).den ∣ C13T29_den ∧ (C13T29.Pq' d e).den ∣ C13T29_den) := by
  constructor <;> decide +kernel
#print axioms C13T29_ok
#print axioms C13T29_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
