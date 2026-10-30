import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type cbc1ecf87282556c4fd0793a9cf634e9dbfbb982eed77bedfc0b8743501f97fd, root class 3. -/
def C3T25 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 5) | 1 => (-59 / 60) | 2 => (-971 / 1140) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | 1 => (-4681 / 3600) | 2 => (-1541341 / 1299600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-12378125 / 97467264) | 1, 1 => 1 | 1, 2 => (-491375 / 8122272) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (12378125 / 97467264) | 1, 1 => 1 | 1, 2 => (491375 / 8122272) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C3T25_ok : C3T25.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T25_den : ℕ := 97467264
theorem C3T25_den_ok :
    (∀ d ∈ C3T25.R, ∀ e ∈ C3T25.R, (C3T25.Lq d e).den ∣ C3T25_den ∧ (C3T25.Lq' d e).den ∣ C3T25_den) ∧
    (∀ d ∈ C3T25.C, ∀ e ∈ C3T25.C, (C3T25.Pq d e).den ∣ C3T25_den ∧ (C3T25.Pq' d e).den ∣ C3T25_den) := by
  constructor <;> decide +kernel
theorem C3T25_cload_2 : C3T25.cload 2 = ((79192639 / 97467264), (-6238601 / 10152840)) := by decide +kernel
#print axioms C3T25_ok
#print axioms C3T25_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
