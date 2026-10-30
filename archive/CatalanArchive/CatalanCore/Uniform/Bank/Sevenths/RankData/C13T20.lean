import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 992224ff61dcfc6097b2e96bbafed76ea41701fc1314c9beea66f3530a834a82, root class 13. -/
def C13T20 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | 2 => (-8 / 39) | 3 => (-173 / 780) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | 2 => (-610 / 1521) | 3 => (-27881 / 67600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-6541 / 8010) | 1, 1 => 1 | 1, 3 => (-2233 / 6942) | 2, 2 => 1 | 2, 3 => (-529 / 2670) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (6541 / 8010) | 1, 1 => 1 | 1, 3 => (2233 / 6942) | 2, 2 => 1 | 2, 3 => (529 / 2670) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C13T20_ok : C13T20.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T20_den : ℕ := 104130
theorem C13T20_den_ok :
    (∀ d ∈ C13T20.R, ∀ e ∈ C13T20.R, (C13T20.Lq d e).den ∣ C13T20_den ∧ (C13T20.Lq' d e).den ∣ C13T20_den) ∧
    (∀ d ∈ C13T20.C, ∀ e ∈ C13T20.C, (C13T20.Pq d e).den ∣ C13T20_den ∧ (C13T20.Pq' d e).den ∣ C13T20_den) := by
  constructor <;> decide +kernel
theorem C13T20_cload_3 : C13T20.cload 3 = ((-35029 / 104130), (-4427 / 34710)) := by decide +kernel
#print axioms C13T20_ok
#print axioms C13T20_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
