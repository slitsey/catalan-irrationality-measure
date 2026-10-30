import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c747aab8afbe32810155c271488b0cde7d502744a426037ee07e3a566bf97acf, root class 13. -/
def C13T31 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 6) | 1 => (-55 / 78) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | 1 => (-3961 / 6084) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (-216 / 637) | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (216 / 637) | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C13T31_ok : C13T31.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T31_den : ℕ := 637
theorem C13T31_den_ok :
    (∀ d ∈ C13T31.R, ∀ e ∈ C13T31.R, (C13T31.Lq d e).den ∣ C13T31_den ∧ (C13T31.Lq' d e).den ∣ C13T31_den) ∧
    (∀ d ∈ C13T31.C, ∀ e ∈ C13T31.C, (C13T31.Pq d e).den ∣ C13T31_den ∧ (C13T31.Pq' d e).den ∣ C13T31_den) := by
  constructor <;> decide +kernel
theorem C13T31_rload_1 : C13T31.rload 1 = ((421 / 637), (-13 / 42)) := by decide +kernel
#print axioms C13T31_ok
#print axioms C13T31_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
