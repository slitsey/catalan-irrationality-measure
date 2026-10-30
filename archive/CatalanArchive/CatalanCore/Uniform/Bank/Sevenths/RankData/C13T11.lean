import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 756212032bd7f2d3ce2a6a8e6d2c9b872e25c8ab40be50ddc50f50d6057dd50c, root class 13. -/
def C13T11 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | 2 => (-8 / 39) | 3 => (-173 / 780) | 4 => (-811 / 3510) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | 2 => (-610 / 1521) | 3 => (-27881 / 67600) | 4 => (-2569703 / 6160050) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C13T11_ok : C13T11.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T11_den : ℕ := 1
theorem C13T11_den_ok :
    (∀ d ∈ C13T11.R, ∀ e ∈ C13T11.R, (C13T11.Lq d e).den ∣ C13T11_den ∧ (C13T11.Lq' d e).den ∣ C13T11_den) ∧
    (∀ d ∈ C13T11.C, ∀ e ∈ C13T11.C, (C13T11.Pq d e).den ∣ C13T11_den ∧ (C13T11.Pq' d e).den ∣ C13T11_den) := by
  constructor <;> decide +kernel
#print axioms C13T11_ok
#print axioms C13T11_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
