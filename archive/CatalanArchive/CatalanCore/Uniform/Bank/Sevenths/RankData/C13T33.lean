import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 2d859c69a3537e9a18c17cec9860bf89263c62c1028a33f1357237ab731436b3, root class 13. -/
def C13T33 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | _ => 0
  Lq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C13T33_ok : C13T33.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T33_den : ℕ := 1
theorem C13T33_den_ok :
    (∀ d ∈ C13T33.R, ∀ e ∈ C13T33.R, (C13T33.Lq d e).den ∣ C13T33_den ∧ (C13T33.Lq' d e).den ∣ C13T33_den) ∧
    (∀ d ∈ C13T33.C, ∀ e ∈ C13T33.C, (C13T33.Pq d e).den ∣ C13T33_den ∧ (C13T33.Pq' d e).den ∣ C13T33_den) := by
  constructor <;> decide +kernel
theorem C13T33_rload_1 : C13T33.rload 1 = (1, 0) := by decide +kernel
#print axioms C13T33_ok
#print axioms C13T33_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
