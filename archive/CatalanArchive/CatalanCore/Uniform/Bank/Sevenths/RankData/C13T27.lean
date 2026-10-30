import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type f0eaaebf17d44846b7681f98512623fa85e6618a637ef73b8ed22433b997388e, root class 13. -/
def C13T27 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | 2 => (-8 / 39) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | 2 => (-610 / 1521) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-61 / 39) | 1, 1 => 1 | 1, 2 => (-8 / 13) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (61 / 39) | 1, 1 => 1 | 1, 2 => (8 / 13) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C13T27_ok : C13T27.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T27_den : ℕ := 39
theorem C13T27_den_ok :
    (∀ d ∈ C13T27.R, ∀ e ∈ C13T27.R, (C13T27.Lq d e).den ∣ C13T27_den ∧ (C13T27.Lq' d e).den ∣ C13T27_den) ∧
    (∀ d ∈ C13T27.C, ∀ e ∈ C13T27.C, (C13T27.Pq d e).den ∣ C13T27_den ∧ (C13T27.Pq' d e).den ∣ C13T27_den) := by
  constructor <;> decide +kernel
theorem C13T27_cload_2 : C13T27.cload 2 = ((-46 / 39), (-4 / 39)) := by decide +kernel
#print axioms C13T27_ok
#print axioms C13T27_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
