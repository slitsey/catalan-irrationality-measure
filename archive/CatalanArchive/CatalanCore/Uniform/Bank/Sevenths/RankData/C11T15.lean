import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 5fdcc7076527d0f59548a4678cf2959b0fbf3503f09e47e885e42064a60a6973, root class 11. -/
def C11T15 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | 2 => (-25 / 9) | 3 => (-415 / 144) | 4 => (-9725 / 3312) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | 2 => (-940 / 81) | 3 => (-242305 / 20736) | 4 => (-128509825 / 10969344) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-381783503287 / 403133245200) | 1, 1 => 1 | 1, 4 => (-69664229291 / 345542781600) | 2, 2 => 1 | 2, 4 => (-30109850483 / 268755496800) | 3, 3 => 1 | 3, 4 => (-867847731 / 11198145700) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (381783503287 / 403133245200) | 1, 1 => 1 | 1, 4 => (69664229291 / 345542781600) | 2, 2 => 1 | 2, 4 => (30109850483 / 268755496800) | 3, 3 => 1 | 3, 4 => (867847731 / 11198145700) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C11T15_ok : C11T15.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T15_den : ℕ := 2418799471200
theorem C11T15_den_ok :
    (∀ d ∈ C11T15.R, ∀ e ∈ C11T15.R, (C11T15.Lq d e).den ∣ C11T15_den ∧ (C11T15.Lq' d e).den ∣ C11T15_den) ∧
    (∀ d ∈ C11T15.C, ∀ e ∈ C11T15.C, (C11T15.Pq d e).den ∣ C11T15_den ∧ (C11T15.Pq' d e).den ∣ C11T15_den) := by
  constructor <;> decide +kernel
theorem C11T15_cload_4 : C11T15.cload 4 = ((-408997458901 / 1209399735600), (-918039340807 / 483759894240)) := by decide +kernel
#print axioms C11T15_ok
#print axioms C11T15_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
