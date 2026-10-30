import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 41c45a11f8cc6dd19765cbb26d37567e2077084008e7dd13a5d97e22e98ede7b, root class 13. -/
def C13T24 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 6) | 1 => (-55 / 78) | 2 => (-433 / 780) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | 1 => (-3961 / 6084) | 2 => (-318529 / 608400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-739395 / 3833258) | 2, 1 => (-69039 / 737165) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (739395 / 3833258) | 2, 1 => (69039 / 737165) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C13T24_ok : C13T24.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T24_den : ℕ := 19166290
theorem C13T24_den_ok :
    (∀ d ∈ C13T24.R, ∀ e ∈ C13T24.R, (C13T24.Lq d e).den ∣ C13T24_den ∧ (C13T24.Lq' d e).den ∣ C13T24_den) ∧
    (∀ d ∈ C13T24.C, ∀ e ∈ C13T24.C, (C13T24.Pq d e).den ∣ C13T24_den ∧ (C13T24.Pq' d e).den ∣ C13T24_den) := by
  constructor <;> decide +kernel
theorem C13T24_rload_2 : C13T24.rload 2 = ((13674301 / 19166290), (-1167899 / 4422990)) := by decide +kernel
#print axioms C13T24_ok
#print axioms C13T24_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
