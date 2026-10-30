import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type e53e3ea3329c902082ed31983b6bd4832e8dfbe692cd18cefc5e7a476e6d8cd0, root class 13. -/
def C13T25 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 6) | 1 => (-55 / 78) | 2 => (-433 / 780) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | 1 => (-3961 / 6084) | 2 => (-318529 / 608400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-739395 / 3833258) | 1, 1 => 1 | 1, 2 => (-69039 / 737165) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (739395 / 3833258) | 1, 1 => 1 | 1, 2 => (69039 / 737165) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C13T25_ok : C13T25.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T25_den : ℕ := 19166290
theorem C13T25_den_ok :
    (∀ d ∈ C13T25.R, ∀ e ∈ C13T25.R, (C13T25.Lq d e).den ∣ C13T25_den ∧ (C13T25.Lq' d e).den ∣ C13T25_den) ∧
    (∀ d ∈ C13T25.C, ∀ e ∈ C13T25.C, (C13T25.Pq d e).den ∣ C13T25_den ∧ (C13T25.Pq' d e).den ∣ C13T25_den) := by
  constructor <;> decide +kernel
theorem C13T25_cload_2 : C13T25.cload 2 = ((13674301 / 19166290), (-1167899 / 4422990)) := by decide +kernel
#print axioms C13T25_ok
#print axioms C13T25_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
