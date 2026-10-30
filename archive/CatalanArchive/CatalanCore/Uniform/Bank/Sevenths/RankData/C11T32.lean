import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 9e32cd98e5db8bca1e220ffab52df03e041cf85284066b688377bf0254d46618, root class 11. -/
def C11T32 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 2) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C11T32_ok : C11T32.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T32_den : ℕ := 1
theorem C11T32_den_ok :
    (∀ d ∈ C11T32.R, ∀ e ∈ C11T32.R, (C11T32.Lq d e).den ∣ C11T32_den ∧ (C11T32.Lq' d e).den ∣ C11T32_den) ∧
    (∀ d ∈ C11T32.C, ∀ e ∈ C11T32.C, (C11T32.Pq d e).den ∣ C11T32_den ∧ (C11T32.Pq' d e).den ∣ C11T32_den) := by
  constructor <;> decide +kernel
#print axioms C11T32_ok
#print axioms C11T32_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
