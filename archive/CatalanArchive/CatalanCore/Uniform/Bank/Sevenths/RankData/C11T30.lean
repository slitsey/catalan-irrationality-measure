import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 7e04543728f9f093b558053228968d4d05ed2f712f073c5d64d26f0730f7bfc8, root class 11. -/
def C11T30 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 2) | 1 => (-59 / 18) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | 1 => (-3841 / 324) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (-8 / 441) | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (8 / 441) | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C11T30_ok : C11T30.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T30_den : ℕ := 441
theorem C11T30_den_ok :
    (∀ d ∈ C11T30.R, ∀ e ∈ C11T30.R, (C11T30.Lq d e).den ∣ C11T30_den ∧ (C11T30.Lq' d e).den ∣ C11T30_den) ∧
    (∀ d ∈ C11T30.C, ∀ e ∈ C11T30.C, (C11T30.Pq d e).den ∣ C11T30_den ∧ (C11T30.Pq' d e).den ∣ C11T30_den) := by
  constructor <;> decide +kernel
theorem C11T30_rload_1 : C11T30.rload 1 = ((433 / 441), (-45 / 14)) := by decide +kernel
#print axioms C11T30_ok
#print axioms C11T30_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
