import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type b0c3d2687c7c07c132cba94afb59095105e4ddc8fb9208325ae228cc9da19ce5, root class 5. -/
def C5T17 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | 2 => (-496 / 255) | 3 => (-3883 / 2040) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | 2 => (-315631 / 65025) | 3 => (-20092009 / 4161600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-1181530424167 / 46470659017670) | 1, 1 => 1 | 1, 3 => (-213493829829 / 18588263607068) | 2, 2 => 1 | 2, 3 => (-2011475274 / 273356817751) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (1181530424167 / 46470659017670) | 1, 1 => 1 | 1, 3 => (213493829829 / 18588263607068) | 2, 2 => 1 | 2, 3 => (2011475274 / 273356817751) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C5T17_ok : C5T17.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T17_den : ℕ := 92941318035340
theorem C5T17_den_ok :
    (∀ d ∈ C5T17.R, ∀ e ∈ C5T17.R, (C5T17.Lq d e).den ∣ C5T17_den ∧ (C5T17.Lq' d e).den ∣ C5T17_den) ∧
    (∀ d ∈ C5T17.C, ∀ e ∈ C5T17.C, (C5T17.Pq d e).den ∣ C5T17_den ∧ (C5T17.Pq' d e).den ∣ C5T17_den) := by
  constructor <;> decide +kernel
theorem C5T17_cload_3 : C5T17.cload 3 = ((88826886444701 / 92941318035340), (-41973208914319 / 23235329508835)) := by decide +kernel
#print axioms C5T17_ok
#print axioms C5T17_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
