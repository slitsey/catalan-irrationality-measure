import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 7cdad618ed55b6be9e129ac995e02743e03d28d614211224610b33b233a2c6e7, root class 9. -/
def C9T09 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | 3 => (-373 / 396) | 4 => (-4811 / 4950) | 5 => (-78461 / 79200) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | 3 => (-354025 / 156816) | 4 => (-13926499 / 6125625) | 5 => (-14309985001 / 6272640000) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (-20967485886974136660311069 / 42393660190857871085742750) | 5, 1 => (-5496354090720225126132803 / 33914928152686296868594200) | 5, 2 => (-221646487337388293357569 / 2312381464955883877404150) | 5, 3 => (-155150522625885842567 / 2283833545635440866572) | 5, 4 => (-150120503681650289722 / 2854791932044301083215) | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (20967485886974136660311069 / 42393660190857871085742750) | 5, 1 => (5496354090720225126132803 / 33914928152686296868594200) | 5, 2 => (221646487337388293357569 / 2312381464955883877404150) | 5, 3 => (155150522625885842567 / 2283833545635440866572) | 5, 4 => (150120503681650289722 / 2854791932044301083215) | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := {5}
  kc := ∅

theorem C9T09_ok : C9T09.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T09_den : ℕ := 508723922290294453028913000
theorem C9T09_den_ok :
    (∀ d ∈ C9T09.R, ∀ e ∈ C9T09.R, (C9T09.Lq d e).den ∣ C9T09_den ∧ (C9T09.Lq' d e).den ∣ C9T09_den) ∧
    (∀ d ∈ C9T09.C, ∀ e ∈ C9T09.C, (C9T09.Pq d e).den ∣ C9T09_den ∧ (C9T09.Pq' d e).den ∣ C9T09_den) := by
  constructor <;> decide +kernel
theorem C9T09_rload_5 : C9T09.rload 5 = ((64595300400589858614263297 / 508723922290294453028913000), (-226912852446535843071198047 / 339149281526862968685942000)) := by decide +kernel
#print axioms C9T09_ok
#print axioms C9T09_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
