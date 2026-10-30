import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 6c0922125be18fcf23adbeeabb487314120ff0cc2bf4fe30142fc7b26d12fe1a, root class 13. -/
def C13T26 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | 2 => (-8 / 39) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | 2 => (-610 / 1521) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-61 / 39) | 2, 1 => (-8 / 13) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (61 / 39) | 2, 1 => (8 / 13) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C13T26_ok : C13T26.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T26_den : ℕ := 39
theorem C13T26_den_ok :
    (∀ d ∈ C13T26.R, ∀ e ∈ C13T26.R, (C13T26.Lq d e).den ∣ C13T26_den ∧ (C13T26.Lq' d e).den ∣ C13T26_den) ∧
    (∀ d ∈ C13T26.C, ∀ e ∈ C13T26.C, (C13T26.Pq d e).den ∣ C13T26_den ∧ (C13T26.Pq' d e).den ∣ C13T26_den) := by
  constructor <;> decide +kernel
theorem C13T26_rload_2 : C13T26.rload 2 = ((-46 / 39), (-4 / 39)) := by decide +kernel
#print axioms C13T26_ok
#print axioms C13T26_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
