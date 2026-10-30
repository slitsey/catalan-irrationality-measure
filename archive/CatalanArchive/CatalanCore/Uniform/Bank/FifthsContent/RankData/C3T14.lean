import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 45a24031f6f6a1781f46ea637283a7eaf53a109695e287bba025cb802fca5e20, prime class 3 mod 10. -/
def C3T14 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | 2 => (-12 / 7) | 3 => (-151 / 84) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | 2 => (-270 / 49) | 3 => (-4369 / 784) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-26021 / 23058) | 1, 1 => 1 | 1, 3 => (-6943 / 23058) | 2, 2 => 1 | 2, 3 => (-21 / 122) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (26021 / 23058) | 1, 1 => 1 | 1, 3 => (6943 / 23058) | 2, 2 => 1 | 2, 3 => (21 / 122) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C3T14_ok : C3T14.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T14_den : ℕ := 23058
theorem C3T14_den_ok :
    (∀ d ∈ C3T14.R, ∀ e ∈ C3T14.R, (C3T14.Lq d e).den ∣ C3T14_den ∧ (C3T14.Lq' d e).den ∣ C3T14_den) ∧
    (∀ d ∈ C3T14.C, ∀ e ∈ C3T14.C, (C3T14.Pq d e).den ∣ C3T14_den ∧ (C3T14.Pq' d e).den ∣ C3T14_den) := by
  constructor <;> decide +kernel
theorem C3T14_cload_3 : C3T14.cload 3 = ((-4625 / 7686), (-8077 / 7686)) := by decide +kernel
#print axioms C3T14_ok
#print axioms C3T14_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
