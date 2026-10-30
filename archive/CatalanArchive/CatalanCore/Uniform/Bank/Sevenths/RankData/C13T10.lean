import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c8b51b5e5e92eafd2a4f67ecacd196b4314a9ea21eed3d81c9972477ff1000f4, root class 13. -/
def C13T10 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-7 / 6) | 1 => (-55 / 78) | 2 => (-433 / 780) | 3 => (-3377 / 7020) | 4 => (-13036 / 29835) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | 1 => (-3961 / 6084) | 2 => (-318529 / 608400) | 3 => (-23637649 / 49280400) | 4 => (-1636209559 / 3560508900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C13T10_ok : C13T10.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T10_den : ℕ := 1
theorem C13T10_den_ok :
    (∀ d ∈ C13T10.R, ∀ e ∈ C13T10.R, (C13T10.Lq d e).den ∣ C13T10_den ∧ (C13T10.Lq' d e).den ∣ C13T10_den) ∧
    (∀ d ∈ C13T10.C, ∀ e ∈ C13T10.C, (C13T10.Pq d e).den ∣ C13T10_den ∧ (C13T10.Pq' d e).den ∣ C13T10_den) := by
  constructor <;> decide +kernel
#print axioms C13T10_ok
#print axioms C13T10_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
