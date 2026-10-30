import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 793d7cff6f93e6c9e11e91ff05dc54ad812fe42159ee0cb90da1abdf11741989, root class 9. -/
def C9T24 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | 2 => (-505 / 396) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | 2 => (-371449 / 156816) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-557416 / 7589241) | 2, 1 => (-23600 / 689931) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (557416 / 7589241) | 2, 1 => (23600 / 689931) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C9T24_ok : C9T24.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T24_den : ℕ := 7589241
theorem C9T24_den_ok :
    (∀ d ∈ C9T24.R, ∀ e ∈ C9T24.R, (C9T24.Lq d e).den ∣ C9T24_den ∧ (C9T24.Lq' d e).den ∣ C9T24_den) ∧
    (∀ d ∈ C9T24.C, ∀ e ∈ C9T24.C, (C9T24.Pq d e).den ∣ C9T24_den ∧ (C9T24.Pq' d e).den ∣ C9T24_den) := by
  constructor <;> decide +kernel
theorem C9T24_rload_2 : C9T24.rload 2 = ((6772225 / 7589241), (-1011251 / 919908)) := by decide +kernel
#print axioms C9T24_ok
#print axioms C9T24_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
