import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 7f1140165ccf075e3767d22696dbaa091f7e8dfd4fd915b04c6d1dc54296d69b, prime class 9 mod 10. -/
def C9T00 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | 2 => (-11 / 36) | 3 => (-83 / 252) | 4 => (-410 / 1197) | 5 => (-16799 / 47880) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | 2 => (-805 / 1296) | 3 => (-40489 / 63504) | 4 => (-1846415 / 2865618) | 5 => (-1484932849 / 2292494400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (-52125175065860709091 / 119999646944955470875) | 1, 1 => 1 | 1, 5 => (-3075812786658433357 / 18461484145377764750) | 2, 2 => 1 | 2, 5 => (-719598148064722674 / 7058802761467968875) | 3, 3 => 1 | 3, 5 => (-1256577781636130739 / 17142806706422210125) | 4, 4 => 1 | 4, 5 => (-51600400633613127 / 902252984548537375) | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (52125175065860709091 / 119999646944955470875) | 1, 1 => 1 | 1, 5 => (3075812786658433357 / 18461484145377764750) | 2, 2 => 1 | 2, 5 => (719598148064722674 / 7058802761467968875) | 3, 3 => 1 | 3, 5 => (1256577781636130739 / 17142806706422210125) | 4, 4 => 1 | 4, 5 => (51600400633613127 / 902252984548537375) | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := {5}

theorem C9T00_ok : C9T00.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T00_den : ℕ := 239999293889910941750
theorem C9T00_den_ok :
    (∀ d ∈ C9T00.R, ∀ e ∈ C9T00.R, (C9T00.Lq d e).den ∣ C9T00_den ∧ (C9T00.Lq' d e).den ∣ C9T00_den) ∧
    (∀ d ∈ C9T00.C, ∀ e ∈ C9T00.C, (C9T00.Pq d e).den ∣ C9T00_den ∧ (C9T00.Pq' d e).den ∣ C9T00_den) := by
  constructor <;> decide +kernel
theorem C9T00_cload_5 : C9T00.cload 5 = ((39979244985982396883 / 239999293889910941750), (-1012274274120542065223 / 4319987290018396951500)) := by decide +kernel
#print axioms C9T00_ok
#print axioms C9T00_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
