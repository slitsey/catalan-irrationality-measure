import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d16d307e71e889cd93f59177a98621d175730af8c6266aa5da0067eec8f88867, root class 5. -/
def C5T12 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | 2 => (-496 / 255) | 3 => (-3883 / 2040) | 4 => (-118843 / 63240) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | 2 => (-315631 / 65025) | 3 => (-20092009 / 4161600) | 4 => (-19262382949 / 3999297600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-64373064632147134599 / 3212911365484285121440) | 1, 1 => 1 | 1, 4 => (-53492025636769289 / 5922417263565502528) | 2, 2 => 1 | 2, 4 => (-109281420760122753 / 18899478620495794832) | 3, 3 => 1 | 3, 4 => (-80228994207626637 / 18899478620495794832) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (64373064632147134599 / 3212911365484285121440) | 1, 1 => 1 | 1, 4 => (53492025636769289 / 5922417263565502528) | 2, 2 => 1 | 2, 4 => (109281420760122753 / 18899478620495794832) | 3, 3 => 1 | 3, 4 => (80228994207626637 / 18899478620495794832) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C5T12_ok : C5T12.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T12_den : ℕ := 6425822730968570242880
theorem C5T12_den_ok :
    (∀ d ∈ C5T12.R, ∀ e ∈ C5T12.R, (C5T12.Lq d e).den ∣ C5T12_den ∧ (C5T12.Lq' d e).den ∣ C5T12_den) ∧
    (∀ d ∈ C5T12.C, ∀ e ∈ C5T12.C, (C5T12.Pq d e).den ∣ C5T12_den ∧ (C5T12.Pq' d e).den ∣ C5T12_den) := by
  constructor <;> decide +kernel
theorem C5T12_cload_4 : C5T12.cload 4 = ((6174604212799346502517 / 6425822730968570242880), (-180203690492799970109 / 100403480171383910045)) := by decide +kernel
#print axioms C5T12_ok
#print axioms C5T12_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
