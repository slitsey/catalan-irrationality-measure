import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 0d7dd81fd19641f23c06abe8b624e693ed2a13e45f6ea9a8d74e37900feb1ea9, root class 11. -/
def C11T26 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 2) | 1 => (-59 / 18) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | 1 => (-3841 / 324) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C11T26_ok : C11T26.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T26_den : ℕ := 1
theorem C11T26_den_ok :
    (∀ d ∈ C11T26.R, ∀ e ∈ C11T26.R, (C11T26.Lq d e).den ∣ C11T26_den ∧ (C11T26.Lq' d e).den ∣ C11T26_den) ∧
    (∀ d ∈ C11T26.C, ∀ e ∈ C11T26.C, (C11T26.Pq d e).den ∣ C11T26_den ∧ (C11T26.Pq' d e).den ∣ C11T26_den) := by
  constructor <;> decide +kernel
#print axioms C11T26_ok
#print axioms C11T26_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
