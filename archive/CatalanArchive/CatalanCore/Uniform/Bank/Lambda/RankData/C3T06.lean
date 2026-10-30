import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d9acc3c4a627f071f4bbaa715afed3fed337a4cce848e76cd16df4cb083a11ef, root class 3. -/
def C3T06 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-4 / 3) | 1 => (-19 / 21) | 2 => (-355 / 462) | 3 => (-1621 / 2310) | 4 => (-58133 / 87780) | _ => 0
  ee := fun d => match d with | 0 => (-16 / 9) | 1 => (-487 / 441) | 2 => (-210571 / 213444) | 3 => (-5050831 / 5336100) | 4 => (-7153327339 / 7705328400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-28504637062415967039 / 359976695801960318620) | 1, 1 => 1 | 1, 4 => (-485192605178533829 / 12856310564355725665) | 2, 2 => 1 | 2, 4 => (-115325472372357399 / 4675022023402082060) | 3, 3 => 1 | 3, 4 => (-8557877838057651 / 467502202340208206) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (28504637062415967039 / 359976695801960318620) | 1, 1 => 1 | 1, 4 => (485192605178533829 / 12856310564355725665) | 2, 2 => 1 | 2, 4 => (115325472372357399 / 4675022023402082060) | 3, 3 => 1 | 3, 4 => (8557877838057651 / 467502202340208206) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C3T06_ok : C3T06.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T06_den : ℕ := 359976695801960318620
theorem C3T06_den_ok :
    (∀ d ∈ C3T06.R, ∀ e ∈ C3T06.R, (C3T06.Lq d e).den ∣ C3T06_den ∧ (C3T06.Lq' d e).den ∣ C3T06_den) ∧
    (∀ d ∈ C3T06.C, ∀ e ∈ C3T06.C, (C3T06.Pq d e).den ∣ C3T06_den ∧ (C3T06.Pq' d e).den ∣ C3T06_den) := by
  constructor <;> decide +kernel
theorem C3T06_cload_4 : C3T06.cload 4 = ((75604259621642373344 / 89994173950490079655), (-6423714826532779939 / 13090061665525829768)) := by decide +kernel
#print axioms C3T06_ok
#print axioms C3T06_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
