import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 46cb636ded44d9a000f76b7c429a0b8a83610c5a22884b72930328f46ea34415, root class 5. -/
def C5T08 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | 2 => (-23 / 15) | 3 => (-137 / 85) | 4 => (-3373 / 2040) | 5 => (-21239 / 12648) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | 2 => (-1054 / 225) | 3 => (-102802 / 21675) | 4 => (-19831909 / 4161600) | 5 => (-3820482209 / 799859520) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (-3643881849968619104943 / 6406403291402927140120) | 1, 1 => 1 | 1, 5 => (-15618251775441905679 / 98560050636968109848) | 2, 2 => 1 | 2, 5 => (-233635856208580674023 / 2562561316561170856048) | 3, 3 => 1 | 3, 5 => (-9633411258965236131 / 150738900974186520944) | 4, 4 => 1 | 4, 5 => (-463308067835382537 / 9421181310886657559) | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (3643881849968619104943 / 6406403291402927140120) | 1, 1 => 1 | 1, 5 => (15618251775441905679 / 98560050636968109848) | 2, 2 => 1 | 2, 5 => (233635856208580674023 / 2562561316561170856048) | 3, 3 => 1 | 3, 5 => (9633411258965236131 / 150738900974186520944) | 4, 4 => 1 | 4, 5 => (463308067835382537 / 9421181310886657559) | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := {5}

theorem C5T08_ok : C5T08.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T08_den : ℕ := 12812806582805854280240
theorem C5T08_den_ok :
    (∀ d ∈ C5T08.R, ∀ e ∈ C5T08.R, (C5T08.Lq d e).den ∣ C5T08_den ∧ (C5T08.Lq' d e).den ∣ C5T08_den) ∧
    (∀ d ∈ C5T08.C, ∀ e ∈ C5T08.C, (C5T08.Pq d e).den ∣ C5T08_den ∧ (C5T08.Pq' d e).den ∣ C5T08_den) := by
  constructor <;> decide +kernel
theorem C5T08_cload_5 : C5T08.cload 5 = ((438775970875049820257 / 6406403291402927140120), (-7327887412246007402443 / 6406403291402927140120)) := by decide +kernel
#print axioms C5T08_ok
#print axioms C5T08_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
