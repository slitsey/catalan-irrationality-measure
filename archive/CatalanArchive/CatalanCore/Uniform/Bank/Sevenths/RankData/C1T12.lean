import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 02353d9d6f561b7e5455ae21610b17838f9a9ba392e16ebc2ff5f4aa75c7e070, root class 1. -/
def C1T12 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-7) | 1 => (-55 / 8) | 2 => (-821 / 120) | 3 => (-9011 / 1320) | 4 => (-260989 / 38280) | _ => 0
  ee := fun d => match d with | 0 => (-49) | 1 => (-3121 / 64) | 2 => (-701761 / 14400) | 3 => (-28298627 / 580800) | 4 => (-23797076207 / 488452800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-2329108155882971245199 / 2511106813968190669982520) | 1, 1 => 1 | 1, 4 => (-52156118786498873797 / 134523579319724500177635) | 2, 2 => 1 | 2, 4 => (-30393683812561366841 / 125555340698409533499126) | 3, 3 => 1 | 3, 4 => (-111326810991412645 / 634117882315199664137) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (2329108155882971245199 / 2511106813968190669982520) | 1, 1 => 1 | 1, 4 => (52156118786498873797 / 134523579319724500177635) | 2, 2 => 1 | 2, 4 => (30393683812561366841 / 125555340698409533499126) | 3, 3 => 1 | 3, 4 => (111326810991412645 / 634117882315199664137) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C1T12_ok : C1T12.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T12_den : ℕ := 7533320441904572009947560
theorem C1T12_den_ok :
    (∀ d ∈ C1T12.R, ∀ e ∈ C1T12.R, (C1T12.Lq d e).den ∣ C1T12_den ∧ (C1T12.Lq' d e).den ∣ C1T12_den) ∧
    (∀ d ∈ C1T12.C, ∀ e ∈ C1T12.C, (C1T12.Pq d e).den ∣ C1T12_den ∧ (C1T12.Pq' d e).den ∣ C1T12_den) := by
  constructor <;> decide +kernel
theorem C1T12_cload_4 : C1T12.cload 4 = ((7520266191241547495046271 / 7533320441904572009947560), (-34180591495347838975550029 / 5022213627936381339965040)) := by decide +kernel
#print axioms C1T12_ok
#print axioms C1T12_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
