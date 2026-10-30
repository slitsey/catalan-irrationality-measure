import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type efe7481185ebc32c542346447b6cbc57f99d155e81d3b6a7f28e0641c6838456, prime class 1 mod 10. -/
def C1T09 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-4) | 2 => (-13 / 3) | 3 => (-49 / 11) | 4 => (-795 / 176) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24) | 2 => (-220 / 9) | 3 => (-8908 / 363) | 4 => (-2283715 / 92928) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-464989640831 / 383175597904) | 1, 1 => 1 | 1, 4 => (-28342887193 / 143690849214) | 2, 2 => 1 | 2, 4 => (-81889825351 / 766351195808) | 3, 3 => 1 | 3, 4 => (-2551058613 / 34834145264) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (464989640831 / 383175597904) | 1, 1 => 1 | 1, 4 => (28342887193 / 143690849214) | 2, 2 => 1 | 2, 4 => (81889825351 / 766351195808) | 3, 3 => 1 | 3, 4 => (2551058613 / 34834145264) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C1T09_ok : C1T09.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T09_den : ℕ := 2299053587424
theorem C1T09_den_ok :
    (∀ d ∈ C1T09.R, ∀ e ∈ C1T09.R, (C1T09.Lq d e).den ∣ C1T09_den ∧ (C1T09.Lq' d e).den ∣ C1T09_den) ∧
    (∀ d ∈ C1T09.C, ∀ e ∈ C1T09.C, (C1T09.Pq d e).den ∣ C1T09_den ∧ (C1T09.Pq' d e).den ∣ C1T09_den) := by
  constructor <;> decide +kernel
theorem C1T09_cload_4 : C1T09.cload 4 = ((-1358409797161 / 2299053587424), (-6756405814693 / 2299053587424)) := by decide +kernel
#print axioms C1T09_ok
#print axioms C1T09_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
