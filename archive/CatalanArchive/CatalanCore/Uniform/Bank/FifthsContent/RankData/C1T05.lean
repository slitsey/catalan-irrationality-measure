import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 62dc8afc058922aabea70087953b315ae414f6c54e213bfd3cd8e38e8fed0145, prime class 1 mod 10. -/
def C1T05 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-5) | 1 => (-29 / 6) | 2 => (-158 / 33) | 3 => (-839 / 176) | 4 => (-17575 / 3696) | _ => 0
  ee := fun d => match d with | 0 => (-25) | 1 => (-889 / 36) | 2 => (-26845 / 1089) | 3 => (-2289523 / 92928) | 4 => (-336480505 / 13660416) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-12305031551098743 / 5048332412954989312) | 4, 1 => (-10472096285838013 / 10096664825909978624) | 4, 2 => (-74718821574681 / 114734827567158848) | 4, 3 => (-54334591303791 / 114734827567158848) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (12305031551098743 / 5048332412954989312) | 4, 1 => (10472096285838013 / 10096664825909978624) | 4, 2 => (74718821574681 / 114734827567158848) | 4, 3 => (54334591303791 / 114734827567158848) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C1T05_ok : C1T05.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T05_den : ℕ := 10096664825909978624
theorem C1T05_den_ok :
    (∀ d ∈ C1T05.R, ∀ e ∈ C1T05.R, (C1T05.Lq d e).den ∣ C1T05_den ∧ (C1T05.Lq' d e).den ∣ C1T05_den) ∧
    (∀ d ∈ C1T05.C, ∀ e ∈ C1T05.C, (C1T05.Pq d e).den ∣ C1T05_den ∧ (C1T05.Pq' d e).den ∣ C1T05_den) := by
  constructor <;> decide +kernel
theorem C1T05_rload_4 : C1T05.rload 4 = ((10050225966188637589 / 10096664825909978624), (-1085980032610694327 / 229469655134317696)) := by decide +kernel
#print axioms C1T05_ok
#print axioms C1T05_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
