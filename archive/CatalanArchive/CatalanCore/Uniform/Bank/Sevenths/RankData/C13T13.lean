import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type f5d5a1db372e49da7ad6ac25b735def91aacbb525dabd4b9c886c0584545bcc2, root class 13. -/
def C13T13 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-7 / 6) | 1 => (-55 / 78) | 2 => (-433 / 780) | 3 => (-3377 / 7020) | 4 => (-13036 / 29835) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | 1 => (-3961 / 6084) | 2 => (-318529 / 608400) | 3 => (-23637649 / 49280400) | 4 => (-1636209559 / 3560508900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-3377648778938836739 / 32130541611540448440) | 1, 1 => 1 | 1, 4 => (-2691262154602283 / 52962431227813926) | 2, 2 => 1 | 2, 4 => (-8256048641273819 / 247158012396464988) | 3, 3 => 1 | 3, 4 => (-60245985476973 / 2423117768592794) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (3377648778938836739 / 32130541611540448440) | 1, 1 => 1 | 1, 4 => (2691262154602283 / 52962431227813926) | 2, 2 => 1 | 2, 4 => (8256048641273819 / 247158012396464988) | 3, 3 => 1 | 3, 4 => (60245985476973 / 2423117768592794) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C13T13_ok : C13T13.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T13_den : ℕ := 96391624834621345320
theorem C13T13_den_ok :
    (∀ d ∈ C13T13.R, ∀ e ∈ C13T13.R, (C13T13.Lq d e).den ∣ C13T13_den ∧ (C13T13.Lq' d e).den ∣ C13T13_den) ∧
    (∀ d ∈ C13T13.C, ∀ e ∈ C13T13.C, (C13T13.Pq d e).den ∣ C13T13_den ∧ (C13T13.Pq' d e).den ∣ C13T13_den) := by
  constructor <;> decide +kernel
theorem C13T13_cload_4 : C13T13.cload 4 = ((75744137104057904693 / 96391624834621345320), (-2655682076987821727 / 10710180537180149480)) := by decide +kernel
#print axioms C13T13_ok
#print axioms C13T13_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
