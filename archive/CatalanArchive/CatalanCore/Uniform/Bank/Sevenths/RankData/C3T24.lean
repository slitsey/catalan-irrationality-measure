import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 2c164b2572e671144521b77f98f4ebfe72c47650414e778f342c61c8c410cd6e, root class 3. -/
def C3T24 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 5) | 1 => (-59 / 60) | 2 => (-971 / 1140) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | 1 => (-4681 / 3600) | 2 => (-1541341 / 1299600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-12378125 / 97467264) | 2, 1 => (-491375 / 8122272) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (12378125 / 97467264) | 2, 1 => (491375 / 8122272) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C3T24_ok : C3T24.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T24_den : ℕ := 97467264
theorem C3T24_den_ok :
    (∀ d ∈ C3T24.R, ∀ e ∈ C3T24.R, (C3T24.Lq d e).den ∣ C3T24_den ∧ (C3T24.Lq' d e).den ∣ C3T24_den) ∧
    (∀ d ∈ C3T24.C, ∀ e ∈ C3T24.C, (C3T24.Pq d e).den ∣ C3T24_den ∧ (C3T24.Pq' d e).den ∣ C3T24_den) := by
  constructor <;> decide +kernel
theorem C3T24_rload_2 : C3T24.rload 2 = ((79192639 / 97467264), (-6238601 / 10152840)) := by decide +kernel
#print axioms C3T24_ok
#print axioms C3T24_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
