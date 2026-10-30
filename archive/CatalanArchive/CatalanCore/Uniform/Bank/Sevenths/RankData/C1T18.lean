import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 17f272bb928858da58ac4c13a38fe609eb82b86ea8ba2a601c91c370107536c5, root class 1. -/
def C1T18 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7) | 1 => (-55 / 8) | 2 => (-821 / 120) | 3 => (-9011 / 1320) | _ => 0
  ee := fun d => match d with | 0 => (-49) | 1 => (-3121 / 64) | 2 => (-701761 / 14400) | 3 => (-28298627 / 580800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-166934234359 / 141660518960070) | 3, 1 => (-34982327716 / 70830259480035) | 3, 2 => (-1457469686 / 4722017298669) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (166934234359 / 141660518960070) | 3, 1 => (34982327716 / 70830259480035) | 3, 2 => (1457469686 / 4722017298669) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C1T18_ok : C1T18.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T18_den : ℕ := 141660518960070
theorem C1T18_den_ok :
    (∀ d ∈ C1T18.R, ∀ e ∈ C1T18.R, (C1T18.Lq d e).den ∣ C1T18_den ∧ (C1T18.Lq' d e).den ∣ C1T18_den) ∧
    (∀ d ∈ C1T18.C, ∀ e ∈ C1T18.C, (C1T18.Pq d e).den ∣ C1T18_den ∧ (C1T18.Pq' d e).den ∣ C1T18_den) := by
  constructor <;> decide +kernel
theorem C1T18_rload_3 : C1T18.rload 3 = ((47126631993233 / 47220172986690), (-1286798649003677 / 188880691946760)) := by decide +kernel
#print axioms C1T18_ok
#print axioms C1T18_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
