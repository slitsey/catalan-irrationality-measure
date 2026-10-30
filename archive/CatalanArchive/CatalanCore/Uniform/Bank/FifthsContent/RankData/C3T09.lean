import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 2f52891238c81ecae85dcb55953eb329532e727b00c719ae45195f66be2c39ad, prime class 3 mod 10. -/
def C3T09 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | 2 => (-12 / 7) | 3 => (-151 / 84) | 4 => (-1315 / 714) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | 2 => (-270 / 49) | 3 => (-4369 / 784) | 4 => (-79255 / 14161) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-242973552197 / 314049124368) | 1, 1 => 1 | 1, 4 => (-4632511859 / 22432080312) | 2, 2 => 1 | 2, 4 => (-15890632609 / 134592481872) | 3, 3 => 1 | 3, 4 => (-102880363 / 1246226684) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (242973552197 / 314049124368) | 1, 1 => 1 | 1, 4 => (4632511859 / 22432080312) | 2, 2 => 1 | 2, 4 => (15890632609 / 134592481872) | 3, 3 => 1 | 3, 4 => (102880363 / 1246226684) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C3T09_ok : C3T09.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T09_den : ℕ := 942147373104
theorem C3T09_den_ok :
    (∀ d ∈ C3T09.R, ∀ e ∈ C3T09.R, (C3T09.Lq d e).den ∣ C3T09_den ∧ (C3T09.Lq' d e).den ∣ C3T09_den) ∧
    (∀ d ∈ C3T09.C, ∀ e ∈ C3T09.C, (C3T09.Pq d e).den ∣ C3T09_den ∧ (C3T09.Pq' d e).den ∣ C3T09_den) := by
  constructor <;> decide +kernel
theorem C3T09_cload_4 : C3T09.cload 4 = ((-10646922766 / 58884210819), (-185472856183 / 157024562184)) := by decide +kernel
#print axioms C3T09_ok
#print axioms C3T09_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
