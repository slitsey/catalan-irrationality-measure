import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 7eef5dff4d9f090270a59891946582a46643c3f69ee68dbe41b1d28bbcf92375, prime class 9 mod 10. -/
def C9T16 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5 / 4) | 1 => (-29 / 36) | 2 => (-167 / 252) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | 1 => (-1129 / 1296) | 2 => (-47545 / 63504) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-251240 / 1520127) | 1, 1 => 1 | 1, 2 => (-13456 / 168903) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (251240 / 1520127) | 1, 1 => 1 | 1, 2 => (13456 / 168903) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C9T16_ok : C9T16.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T16_den : ℕ := 1520127
theorem C9T16_den_ok :
    (∀ d ∈ C9T16.R, ∀ e ∈ C9T16.R, (C9T16.Lq d e).den ∣ C9T16_den ∧ (C9T16.Lq' d e).den ∣ C9T16_den) ∧
    (∀ d ∈ C9T16.C, ∀ e ∈ C9T16.C, (C9T16.Pq d e).den ∣ C9T16_den ∧ (C9T16.Pq' d e).den ∣ C9T16_den) := by
  constructor <;> decide +kernel
theorem C9T16_cload_2 : C9T16.cload 2 = ((163969 / 217161), (-264791 / 675612)) := by decide +kernel
#print axioms C9T16_ok
#print axioms C9T16_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
