import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 63e7a7869181f2b1d5fd5f8d16267ae13f92cb98127b0b292ac46f4ea4b7b9df, prime class 1 mod 10. -/
def C1T08 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-4) | 2 => (-13 / 3) | 3 => (-49 / 11) | 4 => (-795 / 176) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24) | 2 => (-220 / 9) | 3 => (-8908 / 363) | 4 => (-2283715 / 92928) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-464989640831 / 383175597904) | 4, 1 => (-28342887193 / 143690849214) | 4, 2 => (-81889825351 / 766351195808) | 4, 3 => (-2551058613 / 34834145264) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (464989640831 / 383175597904) | 4, 1 => (28342887193 / 143690849214) | 4, 2 => (81889825351 / 766351195808) | 4, 3 => (2551058613 / 34834145264) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C1T08_ok : C1T08.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T08_den : ℕ := 2299053587424
theorem C1T08_den_ok :
    (∀ d ∈ C1T08.R, ∀ e ∈ C1T08.R, (C1T08.Lq d e).den ∣ C1T08_den ∧ (C1T08.Lq' d e).den ∣ C1T08_den) ∧
    (∀ d ∈ C1T08.C, ∀ e ∈ C1T08.C, (C1T08.Pq d e).den ∣ C1T08_den ∧ (C1T08.Pq' d e).den ∣ C1T08_den) := by
  constructor <;> decide +kernel
theorem C1T08_rload_4 : C1T08.rload 4 = ((-1358409797161 / 2299053587424), (-6756405814693 / 2299053587424)) := by decide +kernel
#print axioms C1T08_ok
#print axioms C1T08_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
