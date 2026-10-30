import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type e903da7fb60fdaf4f755ee6f2e94c038cf42f73518a058ec47ea6b2d6e82b37c, root class 11. -/
def C11T20 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 2) | 1 => (-59 / 18) | 2 => (-463 / 144) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | 1 => (-3841 / 324) | 2 => (-244609 / 20736) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C11T20_ok : C11T20.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T20_den : ℕ := 1
theorem C11T20_den_ok :
    (∀ d ∈ C11T20.R, ∀ e ∈ C11T20.R, (C11T20.Lq d e).den ∣ C11T20_den ∧ (C11T20.Lq' d e).den ∣ C11T20_den) ∧
    (∀ d ∈ C11T20.C, ∀ e ∈ C11T20.C, (C11T20.Pq d e).den ∣ C11T20_den ∧ (C11T20.Pq' d e).den ∣ C11T20_den) := by
  constructor <;> decide +kernel
#print axioms C11T20_ok
#print axioms C11T20_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
