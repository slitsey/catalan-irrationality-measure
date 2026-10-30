import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type fa83678b69d002018902c1c46684c823c664bd633b3a2f7c72f615d708b3890c, root class 1. -/
def C1T11 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-7) | 1 => (-55 / 8) | 2 => (-821 / 120) | 3 => (-9011 / 1320) | 4 => (-260989 / 38280) | _ => 0
  ee := fun d => match d with | 0 => (-49) | 1 => (-3121 / 64) | 2 => (-701761 / 14400) | 3 => (-28298627 / 580800) | 4 => (-23797076207 / 488452800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-2329108155882971245199 / 2511106813968190669982520) | 4, 1 => (-52156118786498873797 / 134523579319724500177635) | 4, 2 => (-30393683812561366841 / 125555340698409533499126) | 4, 3 => (-111326810991412645 / 634117882315199664137) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (2329108155882971245199 / 2511106813968190669982520) | 4, 1 => (52156118786498873797 / 134523579319724500177635) | 4, 2 => (30393683812561366841 / 125555340698409533499126) | 4, 3 => (111326810991412645 / 634117882315199664137) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C1T11_ok : C1T11.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T11_den : ℕ := 7533320441904572009947560
theorem C1T11_den_ok :
    (∀ d ∈ C1T11.R, ∀ e ∈ C1T11.R, (C1T11.Lq d e).den ∣ C1T11_den ∧ (C1T11.Lq' d e).den ∣ C1T11_den) ∧
    (∀ d ∈ C1T11.C, ∀ e ∈ C1T11.C, (C1T11.Pq d e).den ∣ C1T11_den ∧ (C1T11.Pq' d e).den ∣ C1T11_den) := by
  constructor <;> decide +kernel
theorem C1T11_rload_4 : C1T11.rload 4 = ((7520266191241547495046271 / 7533320441904572009947560), (-34180591495347838975550029 / 5022213627936381339965040)) := by decide +kernel
#print axioms C1T11_ok
#print axioms C1T11_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
