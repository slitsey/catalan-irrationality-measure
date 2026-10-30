import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c3d693da8bbbcdde75f81e14b09ff6c06b768c709bcbd3a9598917cd376c2c4e, root class 13. -/
def C13T15 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | 2 => (-8 / 39) | 3 => (-173 / 780) | 4 => (-811 / 3510) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | 2 => (-610 / 1521) | 3 => (-27881 / 67600) | 4 => (-2569703 / 6160050) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-20564602439 / 36869916720) | 1, 1 => 1 | 1, 4 => (-1737200263 / 7900696440) | 2, 2 => 1 | 2, 4 => (-384198901 / 2836147440) | 3, 3 => 1 | 3, 4 => (-4618191 / 47269124) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (20564602439 / 36869916720) | 1, 1 => 1 | 1, 4 => (1737200263 / 7900696440) | 2, 2 => 1 | 2, 4 => (384198901 / 2836147440) | 3, 3 => 1 | 3, 4 => (4618191 / 47269124) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C13T15_ok : C13T15.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T15_den : ℕ := 110609750160
theorem C13T15_den_ok :
    (∀ d ∈ C13T15.R, ∀ e ∈ C13T15.R, (C13T15.Lq d e).den ∣ C13T15_den ∧ (C13T15.Lq' d e).den ∣ C13T15_den) ∧
    (∀ d ∈ C13T15.C, ∀ e ∈ C13T15.C, (C13T15.Pq d e).den ∣ C13T15_den ∧ (C13T15.Pq' d e).den ∣ C13T15_den) := by
  constructor <;> decide +kernel
theorem C13T15_cload_4 : C13T15.cload 4 = ((-597592459 / 55304875080), (-34258419 / 236345620)) := by decide +kernel
#print axioms C13T15_ok
#print axioms C13T15_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
