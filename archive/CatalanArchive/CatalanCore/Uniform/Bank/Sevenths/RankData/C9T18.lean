import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 1c1ca80bc118ac27f3c9b7aaa6ba38797b15f2a0e5dd99842e1dcc73d4771562, root class 9. -/
def C9T18 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | 2 => (-505 / 396) | 3 => (-12097 / 9900) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | 2 => (-371449 / 156816) | 3 => (-228949609 / 98010000) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-11167687421584 / 209530759246875) | 3, 1 => (-18855299176 / 761930033625) | 3, 2 => (-33892974784 / 2116472315625) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (11167687421584 / 209530759246875) | 3, 1 => (18855299176 / 761930033625) | 3, 2 => (33892974784 / 2116472315625) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C9T18_ok : C9T18.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T18_den : ℕ := 209530759246875
theorem C9T18_den_ok :
    (∀ d ∈ C9T18.R, ∀ e ∈ C9T18.R, (C9T18.Lq d e).den ∣ C9T18_den ∧ (C9T18.Lq' d e).den ∣ C9T18_den) ∧
    (∀ d ∈ C9T18.C, ∀ e ∈ C9T18.C, (C9T18.Pq d e).den ∣ C9T18_den ∧ (C9T18.Pq' d e).den ∣ C9T18_den) := by
  constructor <;> decide +kernel
theorem C9T18_rload_3 : C9T18.rload 3 = ((2530966133977 / 2793743456625), (-300024842874739 / 279374345662500)) := by decide +kernel
#print axioms C9T18_ok
#print axioms C9T18_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
