import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 88fd95b53654c43bd22ff310384de410ac8ae80f124f9b3ceeff52bf06fc91d1, prime class 1 mod 10. -/
def C1T16 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-4) | 2 => (-13 / 3) | 3 => (-49 / 11) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24) | 2 => (-220 / 9) | 3 => (-8908 / 363) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-1068959 / 605352) | 3, 1 => (-115823 / 403568) | 3, 2 => (-713 / 4586) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (1068959 / 605352) | 3, 1 => (115823 / 403568) | 3, 2 => (713 / 4586) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C1T16_ok : C1T16.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T16_den : ℕ := 1210704
theorem C1T16_den_ok :
    (∀ d ∈ C1T16.R, ∀ e ∈ C1T16.R, (C1T16.Lq d e).den ∣ C1T16_den ∧ (C1T16.Lq' d e).den ∣ C1T16_den) ∧
    (∀ d ∈ C1T16.C, ∀ e ∈ C1T16.C, (C1T16.Pq d e).den ∣ C1T16_den ∧ (C1T16.Pq' d e).den ∣ C1T16_den) := by
  constructor <;> decide +kernel
theorem C1T16_rload_3 : C1T16.rload 3 = ((-1462915 / 1210704), (-796897 / 302676)) := by decide +kernel
#print axioms C1T16_ok
#print axioms C1T16_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
