import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 95799a4e896864766f174c98ab1bd012505960b687d2053798be31999796fe0a, root class 9. -/
def C9T08 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | 3 => (-373 / 396) | 4 => (-4811 / 4950) | 5 => (-78461 / 79200) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | 3 => (-354025 / 156816) | 4 => (-13926499 / 6125625) | 5 => (-14309985001 / 6272640000) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (-20967485886974136660311069 / 42393660190857871085742750) | 1, 1 => 1 | 1, 5 => (-5496354090720225126132803 / 33914928152686296868594200) | 2, 2 => 1 | 2, 5 => (-221646487337388293357569 / 2312381464955883877404150) | 3, 3 => 1 | 3, 5 => (-155150522625885842567 / 2283833545635440866572) | 4, 4 => 1 | 4, 5 => (-150120503681650289722 / 2854791932044301083215) | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (20967485886974136660311069 / 42393660190857871085742750) | 1, 1 => 1 | 1, 5 => (5496354090720225126132803 / 33914928152686296868594200) | 2, 2 => 1 | 2, 5 => (221646487337388293357569 / 2312381464955883877404150) | 3, 3 => 1 | 3, 5 => (155150522625885842567 / 2283833545635440866572) | 4, 4 => 1 | 4, 5 => (150120503681650289722 / 2854791932044301083215) | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := {5}

theorem C9T08_ok : C9T08.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T08_den : ℕ := 508723922290294453028913000
theorem C9T08_den_ok :
    (∀ d ∈ C9T08.R, ∀ e ∈ C9T08.R, (C9T08.Lq d e).den ∣ C9T08_den ∧ (C9T08.Lq' d e).den ∣ C9T08_den) ∧
    (∀ d ∈ C9T08.C, ∀ e ∈ C9T08.C, (C9T08.Pq d e).den ∣ C9T08_den ∧ (C9T08.Pq' d e).den ∣ C9T08_den) := by
  constructor <;> decide +kernel
theorem C9T08_cload_5 : C9T08.cload 5 = ((64595300400589858614263297 / 508723922290294453028913000), (-226912852446535843071198047 / 339149281526862968685942000)) := by decide +kernel
#print axioms C9T08_ok
#print axioms C9T08_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
