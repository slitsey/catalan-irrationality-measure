import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 9d3015a6deebc9f39649333a95a293b3eb014fafe2d1fa64675605871a05e71c, root class 13. -/
def C13T22 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 6) | 1 => (-55 / 78) | 2 => (-433 / 780) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | 1 => (-3961 / 6084) | 2 => (-318529 / 608400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C13T22_ok : C13T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T22_den : ℕ := 1
theorem C13T22_den_ok :
    (∀ d ∈ C13T22.R, ∀ e ∈ C13T22.R, (C13T22.Lq d e).den ∣ C13T22_den ∧ (C13T22.Lq' d e).den ∣ C13T22_den) ∧
    (∀ d ∈ C13T22.C, ∀ e ∈ C13T22.C, (C13T22.Pq d e).den ∣ C13T22_den ∧ (C13T22.Pq' d e).den ∣ C13T22_den) := by
  constructor <;> decide +kernel
#print axioms C13T22_ok
#print axioms C13T22_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
