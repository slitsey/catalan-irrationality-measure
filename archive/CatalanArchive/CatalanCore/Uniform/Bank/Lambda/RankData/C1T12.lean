import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 87ac7b6c0d02a234707961639efc4b4e809211534aeb64f31ef7e72b40c754b0, root class 1. -/
def C1T12 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-4) | 1 => (-19 / 5) | 2 => (-337 / 90) | 3 => (-4351 / 1170) | _ => 0
  ee := fun d => match d with | 0 => (-16) | 1 => (-391 / 25) | 2 => (-126259 / 8100) | 3 => (-21315271 / 1368900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-21487536043 / 3695744099970) | 3, 1 => (-3719111729 / 1478297639988) | 3, 2 => (-65223427 / 41063823333) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (21487536043 / 3695744099970) | 3, 1 => (3719111729 / 1478297639988) | 3, 2 => (65223427 / 41063823333) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C1T12_ok : C1T12.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T12_den : ℕ := 7391488199940
theorem C1T12_den_ok :
    (∀ d ∈ C1T12.R, ∀ e ∈ C1T12.R, (C1T12.Lq d e).den ∣ C1T12_den ∧ (C1T12.Lq' d e).den ∣ C1T12_den) ∧
    (∀ d ∈ C1T12.C, ∀ e ∈ C1T12.C, (C1T12.Pq d e).den ∣ C1T12_den ∧ (C1T12.Pq' d e).den ∣ C1T12_den) := by
  constructor <;> decide +kernel
theorem C1T12_rload_3 : C1T12.rload 3 = ((2439392450783 / 2463829399980), (-9066989195663 / 2463829399980)) := by decide +kernel
#print axioms C1T12_ok
#print axioms C1T12_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
