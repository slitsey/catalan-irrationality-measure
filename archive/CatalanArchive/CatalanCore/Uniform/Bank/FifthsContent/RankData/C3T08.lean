import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type e3419629782a157966133f82c9ca7a3c2b232c350c5c7a4f3174f75831dc31dd, prime class 3 mod 10. -/
def C3T08 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | 2 => (-12 / 7) | 3 => (-151 / 84) | 4 => (-1315 / 714) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | 2 => (-270 / 49) | 3 => (-4369 / 784) | 4 => (-79255 / 14161) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-242973552197 / 314049124368) | 4, 1 => (-4632511859 / 22432080312) | 4, 2 => (-15890632609 / 134592481872) | 4, 3 => (-102880363 / 1246226684) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (242973552197 / 314049124368) | 4, 1 => (4632511859 / 22432080312) | 4, 2 => (15890632609 / 134592481872) | 4, 3 => (102880363 / 1246226684) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C3T08_ok : C3T08.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T08_den : ℕ := 942147373104
theorem C3T08_den_ok :
    (∀ d ∈ C3T08.R, ∀ e ∈ C3T08.R, (C3T08.Lq d e).den ∣ C3T08_den ∧ (C3T08.Lq' d e).den ∣ C3T08_den) ∧
    (∀ d ∈ C3T08.C, ∀ e ∈ C3T08.C, (C3T08.Pq d e).den ∣ C3T08_den ∧ (C3T08.Pq' d e).den ∣ C3T08_den) := by
  constructor <;> decide +kernel
theorem C3T08_rload_4 : C3T08.rload 4 = ((-10646922766 / 58884210819), (-185472856183 / 157024562184)) := by decide +kernel
#print axioms C3T08_ok
#print axioms C3T08_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
