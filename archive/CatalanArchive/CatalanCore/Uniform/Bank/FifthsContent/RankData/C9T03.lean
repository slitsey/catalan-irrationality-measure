import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 827b46ff0a12126daf7f1360ad337211c114caaccdb97bad5dc3dcb9cc49390c, prime class 9 mod 10. -/
def C9T03 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | 2 => (-11 / 36) | 3 => (-83 / 252) | 4 => (-410 / 1197) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | 2 => (-805 / 1296) | 3 => (-40489 / 63504) | 4 => (-1846415 / 2865618) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-1357355999893 / 2380523073957) | 4, 1 => (-1561007058832 / 7141569221871) | 4, 2 => (-106110946868 / 793507691319) | 4, 3 => (-3632942928 / 37786080539) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (1357355999893 / 2380523073957) | 4, 1 => (1561007058832 / 7141569221871) | 4, 2 => (106110946868 / 793507691319) | 4, 3 => (3632942928 / 37786080539) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C9T03_ok : C9T03.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T03_den : ℕ := 7141569221871
theorem C9T03_den_ok :
    (∀ d ∈ C9T03.R, ∀ e ∈ C9T03.R, (C9T03.Lq d e).den ∣ C9T03_den ∧ (C9T03.Lq' d e).den ∣ C9T03_den) ∧
    (∀ d ∈ C9T03.C, ∀ e ∈ C9T03.C, (C9T03.Pq d e).den ∣ C9T03_den ∧ (C9T03.Pq' d e).den ∣ C9T03_den) := by
  constructor <;> decide +kernel
theorem C9T03_rload_4 : C9T03.rload 4 = ((-133130571844 / 7141569221871), (-1537943963767 / 7141569221871)) := by decide +kernel
#print axioms C9T03_ok
#print axioms C9T03_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
