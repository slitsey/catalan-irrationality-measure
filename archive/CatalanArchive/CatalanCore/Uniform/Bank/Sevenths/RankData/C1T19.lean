import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 49693ff82e32cc7e6eb440e6e4ad94852f4bcb9e40f68f0dc7eeb82dadbd5efd, root class 1. -/
def C1T19 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | 2 => (-51 / 8) | 3 => (-781 / 120) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | 2 => (-3105 / 64) | 3 => (-233387 / 4800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T19_ok : C1T19.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T19_den : ℕ := 1
theorem C1T19_den_ok :
    (∀ d ∈ C1T19.R, ∀ e ∈ C1T19.R, (C1T19.Lq d e).den ∣ C1T19_den ∧ (C1T19.Lq' d e).den ∣ C1T19_den) ∧
    (∀ d ∈ C1T19.C, ∀ e ∈ C1T19.C, (C1T19.Pq d e).den ∣ C1T19_den ∧ (C1T19.Pq' d e).den ∣ C1T19_den) := by
  constructor <;> decide +kernel
#print axioms C1T19_ok
#print axioms C1T19_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
