import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type cabbc165f083a89c3144bf34eb7a7ad07be3d808e696638f874ac3ca09c32bc3, root class 13. -/
def C13T07 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | 2 => (-8 / 39) | 3 => (-173 / 780) | 4 => (-811 / 3510) | 5 => (-7069 / 29835) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | 2 => (-610 / 1521) | 3 => (-27881 / 67600) | 4 => (-2569703 / 6160050) | 5 => (-1493789203 / 3560508900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C13T07_ok : C13T07.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T07_den : ℕ := 1
theorem C13T07_den_ok :
    (∀ d ∈ C13T07.R, ∀ e ∈ C13T07.R, (C13T07.Lq d e).den ∣ C13T07_den ∧ (C13T07.Lq' d e).den ∣ C13T07_den) ∧
    (∀ d ∈ C13T07.C, ∀ e ∈ C13T07.C, (C13T07.Pq d e).den ∣ C13T07_den ∧ (C13T07.Pq' d e).den ∣ C13T07_den) := by
  constructor <;> decide +kernel
#print axioms C13T07_ok
#print axioms C13T07_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
