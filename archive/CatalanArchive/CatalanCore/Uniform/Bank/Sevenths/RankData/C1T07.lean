import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type bfa8cbe8d7ae8b63f962f7c6bfe12226db19625da7f12b197448d8eb7e9325c7, root class 1. -/
def C1T07 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | 2 => (-51 / 8) | 3 => (-781 / 120) | 4 => (-8681 / 1320) | 5 => (-253333 / 38280) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | 2 => (-3105 / 64) | 3 => (-233387 / 4800) | 4 => (-28262327 / 580800) | 5 => (-4755507619 / 97690560) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T07_ok : C1T07.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T07_den : ℕ := 1
theorem C1T07_den_ok :
    (∀ d ∈ C1T07.R, ∀ e ∈ C1T07.R, (C1T07.Lq d e).den ∣ C1T07_den ∧ (C1T07.Lq' d e).den ∣ C1T07_den) ∧
    (∀ d ∈ C1T07.C, ∀ e ∈ C1T07.C, (C1T07.Pq d e).den ∣ C1T07_den ∧ (C1T07.Pq' d e).den ∣ C1T07_den) := by
  constructor <;> decide +kernel
#print axioms C1T07_ok
#print axioms C1T07_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
