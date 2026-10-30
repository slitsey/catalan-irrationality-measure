import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 7e26c008100a05dbe4c3c51b689c5b9fdd4658cd4dc7fac827d2d96347536430, root class 3. -/
def C3T19 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 5) | 1 => (-59 / 60) | 2 => (-971 / 1140) | 3 => (-3891 / 4940) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | 1 => (-4681 / 3600) | 2 => (-1541341 / 1299600) | 3 => (-84001043 / 73210800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-85660609905125 / 941279830593531) | 3, 1 => (-13563409044500 / 313759943531177) | 3, 2 => (-466001476750 / 16513681238483) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (85660609905125 / 941279830593531) | 3, 1 => (13563409044500 / 313759943531177) | 3, 2 => (466001476750 / 16513681238483) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C3T19_ok : C3T19.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T19_den : ℕ := 941279830593531
theorem C3T19_den_ok :
    (∀ d ∈ C3T19.R, ∀ e ∈ C3T19.R, (C3T19.Lq d e).den ∣ C3T19_den ∧ (C3T19.Lq' d e).den ∣ C3T19_den) ∧
    (∀ d ∈ C3T19.C, ∀ e ∈ C3T19.C, (C3T19.Pq d e).den ∣ C3T19_den ∧ (C3T19.Pq' d e).den ∣ C3T19_den) := by
  constructor <;> decide +kernel
theorem C3T19_rload_3 : C3T19.rload 3 = ((788366909380156 / 941279830593531), (-11176789824092293 / 18825596611870620)) := by decide +kernel
#print axioms C3T19_ok
#print axioms C3T19_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
