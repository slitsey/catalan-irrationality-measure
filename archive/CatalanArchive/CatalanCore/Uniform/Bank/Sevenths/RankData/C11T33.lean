import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type e8edb73a15d1d6898e858b2d5ab295fa1240467444e1e625a193836027c813f1, root class 11. -/
def C11T33 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C11T33_ok : C11T33.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T33_den : ℕ := 1
theorem C11T33_den_ok :
    (∀ d ∈ C11T33.R, ∀ e ∈ C11T33.R, (C11T33.Lq d e).den ∣ C11T33_den ∧ (C11T33.Lq' d e).den ∣ C11T33_den) ∧
    (∀ d ∈ C11T33.C, ∀ e ∈ C11T33.C, (C11T33.Pq d e).den ∣ C11T33_den ∧ (C11T33.Pq' d e).den ∣ C11T33_den) := by
  constructor <;> decide +kernel
theorem C11T33_cload_1 : C11T33.cload 1 = (1, 0) := by decide +kernel
#print axioms C11T33_ok
#print axioms C11T33_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
