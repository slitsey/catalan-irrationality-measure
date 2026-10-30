import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type a6ebaf53628d3fb85b6fbc8af305912c083ab0f4724d0eac91dcf4daab58a2e2, prime class 9 mod 10. -/
def C9T04 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | 2 => (-11 / 36) | 3 => (-83 / 252) | 4 => (-410 / 1197) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | 2 => (-805 / 1296) | 3 => (-40489 / 63504) | 4 => (-1846415 / 2865618) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-1357355999893 / 2380523073957) | 1, 1 => 1 | 1, 4 => (-1561007058832 / 7141569221871) | 2, 2 => 1 | 2, 4 => (-106110946868 / 793507691319) | 3, 3 => 1 | 3, 4 => (-3632942928 / 37786080539) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (1357355999893 / 2380523073957) | 1, 1 => 1 | 1, 4 => (1561007058832 / 7141569221871) | 2, 2 => 1 | 2, 4 => (106110946868 / 793507691319) | 3, 3 => 1 | 3, 4 => (3632942928 / 37786080539) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C9T04_ok : C9T04.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T04_den : ℕ := 7141569221871
theorem C9T04_den_ok :
    (∀ d ∈ C9T04.R, ∀ e ∈ C9T04.R, (C9T04.Lq d e).den ∣ C9T04_den ∧ (C9T04.Lq' d e).den ∣ C9T04_den) ∧
    (∀ d ∈ C9T04.C, ∀ e ∈ C9T04.C, (C9T04.Pq d e).den ∣ C9T04_den ∧ (C9T04.Pq' d e).den ∣ C9T04_den) := by
  constructor <;> decide +kernel
theorem C9T04_cload_4 : C9T04.cload 4 = ((-133130571844 / 7141569221871), (-1537943963767 / 7141569221871)) := by decide +kernel
#print axioms C9T04_ok
#print axioms C9T04_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
