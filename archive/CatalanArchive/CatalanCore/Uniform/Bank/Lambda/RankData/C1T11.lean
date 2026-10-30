import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 23316490147193e7e314a298c2083a554d7b8b727218638549c974de43663192, root class 1. -/
def C1T11 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-4) | 1 => (-19 / 5) | 2 => (-337 / 90) | 3 => (-4351 / 1170) | _ => 0
  ee := fun d => match d with | 0 => (-16) | 1 => (-391 / 25) | 2 => (-126259 / 8100) | 3 => (-21315271 / 1368900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-21487536043 / 3695744099970) | 1, 1 => 1 | 1, 3 => (-3719111729 / 1478297639988) | 2, 2 => 1 | 2, 3 => (-65223427 / 41063823333) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (21487536043 / 3695744099970) | 1, 1 => 1 | 1, 3 => (3719111729 / 1478297639988) | 2, 2 => 1 | 2, 3 => (65223427 / 41063823333) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C1T11_ok : C1T11.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T11_den : ℕ := 7391488199940
theorem C1T11_den_ok :
    (∀ d ∈ C1T11.R, ∀ e ∈ C1T11.R, (C1T11.Lq d e).den ∣ C1T11_den ∧ (C1T11.Lq' d e).den ∣ C1T11_den) ∧
    (∀ d ∈ C1T11.C, ∀ e ∈ C1T11.C, (C1T11.Pq d e).den ∣ C1T11_den ∧ (C1T11.Pq' d e).den ∣ C1T11_den) := by
  constructor <;> decide +kernel
theorem C1T11_cload_3 : C1T11.cload 3 = ((2439392450783 / 2463829399980), (-9066989195663 / 2463829399980)) := by decide +kernel
#print axioms C1T11_ok
#print axioms C1T11_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
