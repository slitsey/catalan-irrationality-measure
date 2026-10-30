import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 7653aea363c31e74ec28df7b245636103444b433619e677dc207af0fd605591b, root class 1. -/
def C1T24 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7) | 1 => (-55 / 8) | 2 => (-821 / 120) | _ => 0
  ee := fun d => match d with | 0 => (-49) | 1 => (-3121 / 64) | 2 => (-701761 / 14400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-3949 / 2446848) | 1, 1 => 1 | 1, 2 => (-1039 / 1529280) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (3949 / 2446848) | 1, 1 => 1 | 1, 2 => (1039 / 1529280) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C1T24_ok : C1T24.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T24_den : ℕ := 12234240
theorem C1T24_den_ok :
    (∀ d ∈ C1T24.R, ∀ e ∈ C1T24.R, (C1T24.Lq d e).den ∣ C1T24_den ∧ (C1T24.Lq' d e).den ∣ C1T24_den) ∧
    (∀ d ∈ C1T24.C, ∀ e ∈ C1T24.C, (C1T24.Pq d e).den ∣ C1T24_den ∧ (C1T24.Pq' d e).den ∣ C1T24_den) := by
  constructor <;> decide +kernel
theorem C1T24_cload_2 : C1T24.cload 2 = ((12206183 / 12234240), (-869867 / 127440)) := by decide +kernel
#print axioms C1T24_ok
#print axioms C1T24_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
