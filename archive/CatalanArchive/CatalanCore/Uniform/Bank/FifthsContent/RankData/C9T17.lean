import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 5ef27503f218335002fe0124220d8e2c9ae5621f209440cfe5d994ae782f246c, prime class 9 mod 10. -/
def C9T17 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | 2 => (-11 / 36) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | 2 => (-805 / 1296) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-115 / 72) | 2, 1 => (-11 / 18) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (115 / 72) | 2, 1 => (11 / 18) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C9T17_ok : C9T17.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T17_den : ℕ := 72
theorem C9T17_den_ok :
    (∀ d ∈ C9T17.R, ∀ e ∈ C9T17.R, (C9T17.Lq d e).den ∣ C9T17_den ∧ (C9T17.Lq' d e).den ∣ C9T17_den) ∧
    (∀ d ∈ C9T17.C, ∀ e ∈ C9T17.C, (C9T17.Pq d e).den ∣ C9T17_den ∧ (C9T17.Pq' d e).den ∣ C9T17_den) := by
  constructor <;> decide +kernel
theorem C9T17_rload_2 : C9T17.rload 2 = ((-29 / 24), (-11 / 72)) := by decide +kernel
#print axioms C9T17_ok
#print axioms C9T17_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
