import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 5a343fb2754fe6e93d7ea67455b4f6e33078cdf00290d30d729306e840f54fa5, root class 5. -/
def C5T18 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | 2 => (-496 / 255) | 3 => (-3883 / 2040) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | 2 => (-315631 / 65025) | 3 => (-20092009 / 4161600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-1181530424167 / 46470659017670) | 3, 1 => (-213493829829 / 18588263607068) | 3, 2 => (-2011475274 / 273356817751) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (1181530424167 / 46470659017670) | 3, 1 => (213493829829 / 18588263607068) | 3, 2 => (2011475274 / 273356817751) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C5T18_ok : C5T18.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T18_den : ℕ := 92941318035340
theorem C5T18_den_ok :
    (∀ d ∈ C5T18.R, ∀ e ∈ C5T18.R, (C5T18.Lq d e).den ∣ C5T18_den ∧ (C5T18.Lq' d e).den ∣ C5T18_den) ∧
    (∀ d ∈ C5T18.C, ∀ e ∈ C5T18.C, (C5T18.Pq d e).den ∣ C5T18_den ∧ (C5T18.Pq' d e).den ∣ C5T18_den) := by
  constructor <;> decide +kernel
theorem C5T18_rload_3 : C5T18.rload 3 = ((88826886444701 / 92941318035340), (-41973208914319 / 23235329508835)) := by decide +kernel
#print axioms C5T18_ok
#print axioms C5T18_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
