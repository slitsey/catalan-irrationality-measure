import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type a24d64ec8c83c9693c1a13d797adc70f3d72d0144268b0d6f6bd79d7103672fd, root class 13. -/
def C13T14 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | 2 => (-8 / 39) | 3 => (-173 / 780) | 4 => (-811 / 3510) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | 2 => (-610 / 1521) | 3 => (-27881 / 67600) | 4 => (-2569703 / 6160050) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-20564602439 / 36869916720) | 4, 1 => (-1737200263 / 7900696440) | 4, 2 => (-384198901 / 2836147440) | 4, 3 => (-4618191 / 47269124) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (20564602439 / 36869916720) | 4, 1 => (1737200263 / 7900696440) | 4, 2 => (384198901 / 2836147440) | 4, 3 => (4618191 / 47269124) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C13T14_ok : C13T14.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T14_den : ℕ := 110609750160
theorem C13T14_den_ok :
    (∀ d ∈ C13T14.R, ∀ e ∈ C13T14.R, (C13T14.Lq d e).den ∣ C13T14_den ∧ (C13T14.Lq' d e).den ∣ C13T14_den) ∧
    (∀ d ∈ C13T14.C, ∀ e ∈ C13T14.C, (C13T14.Pq d e).den ∣ C13T14_den ∧ (C13T14.Pq' d e).den ∣ C13T14_den) := by
  constructor <;> decide +kernel
theorem C13T14_rload_4 : C13T14.rload 4 = ((-597592459 / 55304875080), (-34258419 / 236345620)) := by decide +kernel
#print axioms C13T14_ok
#print axioms C13T14_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
