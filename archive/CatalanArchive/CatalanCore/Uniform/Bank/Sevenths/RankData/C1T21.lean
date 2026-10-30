import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 2963aada52170324573f944e47dad18493b5dfdc962673e0e05215d5d76cbd88, root class 1. -/
def C1T21 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | 2 => (-51 / 8) | 3 => (-781 / 120) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | 2 => (-3105 / 64) | 3 => (-233387 / 4800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-10540603 / 4605120) | 1, 1 => 1 | 1, 3 => (-2597161 / 9210240) | 2, 2 => 1 | 2, 3 => (-1597 / 10660) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (10540603 / 4605120) | 1, 1 => 1 | 1, 3 => (2597161 / 9210240) | 2, 2 => 1 | 2, 3 => (1597 / 10660) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C1T21_ok : C1T21.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T21_den : ℕ := 9210240
theorem C1T21_den_ok :
    (∀ d ∈ C1T21.R, ∀ e ∈ C1T21.R, (C1T21.Lq d e).den ∣ C1T21_den ∧ (C1T21.Lq' d e).den ∣ C1T21_den) ∧
    (∀ d ∈ C1T21.C, ∀ e ∈ C1T21.C, (C1T21.Pq d e).den ∣ C1T21_den ∧ (C1T21.Pq' d e).den ∣ C1T21_den) := by
  constructor <;> decide +kernel
theorem C1T21_cload_3 : C1T21.cload 3 = ((-25769 / 14976), (-1185469 / 307008)) := by decide +kernel
#print axioms C1T21_ok
#print axioms C1T21_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
