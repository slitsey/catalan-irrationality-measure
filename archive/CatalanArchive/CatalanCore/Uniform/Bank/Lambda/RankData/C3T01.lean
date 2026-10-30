import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type a3810ebed5d692487ad7034342caa8a92d14a38ff64efca07bbb55f660aba9d6, root class 3. -/
def C3T01 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 3) | 2 => (-17 / 42) | 3 => (-67 / 154) | 4 => (-2087 / 4620) | 5 => (-40577 / 87780) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-7 / 9) | 2 => (-1507 / 1764) | 3 => (-62285 / 71148) | 4 => (-18869299 / 21344400) | 5 => (-6845114203 / 7705328400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (-1120798142049549125559 / 2523803370334745327675) | 5, 1 => (-66916557785316335259 / 403808539253559252428) | 5, 2 => (-14527385154274980643 / 144217335447699733010) | 5, 3 => (-1893769372078396143 / 26221333717763587820) | 5, 4 => (-368799679877220216 / 6555333429440896955) | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (1120798142049549125559 / 2523803370334745327675) | 5, 1 => (66916557785316335259 / 403808539253559252428) | 5, 2 => (14527385154274980643 / 144217335447699733010) | 5, 3 => (1893769372078396143 / 26221333717763587820) | 5, 4 => (368799679877220216 / 6555333429440896955) | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := {5}
  kc := ∅

theorem C3T01_ok : C3T01.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T01_den : ℕ := 10095213481338981310700
theorem C3T01_den_ok :
    (∀ d ∈ C3T01.R, ∀ e ∈ C3T01.R, (C3T01.Lq d e).den ∣ C3T01_den ∧ (C3T01.Lq' d e).den ∣ C3T01_den) ∧
    (∀ d ∈ C3T01.C, ∀ e ∈ C3T01.C, (C3T01.Pq d e).den ∣ C3T01_den ∧ (C3T01.Pq' d e).den ∣ C3T01_den) := by
  constructor <;> decide +kernel
theorem C3T01_rload_5 : C3T01.rload 5 = ((58040617587411647653 / 360543338619249332525), (-6247154238882597275657 / 20190426962677962621400)) := by decide +kernel
#print axioms C3T01_ok
#print axioms C3T01_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
