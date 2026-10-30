import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 2e5fff70910d9680fc5aab512b1b5a72699cb32582d4fea17b00684b8b7485de, root class 11. -/
def C11T18 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 2) | 1 => (-59 / 18) | 2 => (-463 / 144) | 3 => (-10553 / 3312) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | 1 => (-3841 / 324) | 2 => (-244609 / 20736) | 3 => (-129195409 / 10969344) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-9649420171 / 1142995805676) | 3, 1 => (-936742331 / 253999067928) | 3, 2 => (-74159396 / 31749883491) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (9649420171 / 1142995805676) | 3, 1 => (936742331 / 253999067928) | 3, 2 => (74159396 / 31749883491) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C11T18_ok : C11T18.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T18_den : ℕ := 2285991611352
theorem C11T18_den_ok :
    (∀ d ∈ C11T18.R, ∀ e ∈ C11T18.R, (C11T18.Lq d e).den ∣ C11T18_den ∧ (C11T18.Lq' d e).den ∣ C11T18_den) ∧
    (∀ d ∈ C11T18.C, ∀ e ∈ C11T18.C, (C11T18.Pq d e).den ∣ C11T18_den ∧ (C11T18.Pq' d e).den ∣ C11T18_den) := by
  constructor <;> decide +kernel
theorem C11T18_rload_3 : C11T18.rload 3 = ((2252922613519 / 2285991611352), (-7171489661615 / 2285991611352)) := by decide +kernel
#print axioms C11T18_ok
#print axioms C11T18_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
