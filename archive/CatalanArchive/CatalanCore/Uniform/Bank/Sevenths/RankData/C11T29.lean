import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type db79d58342a51efc49e63dafc956a3e8b502856fbafab32548484991b9560780, root class 11. -/
def C11T29 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 2) | 1 => (-59 / 18) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | 1 => (-3841 / 324) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (-8 / 441) | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (8 / 441) | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C11T29_ok : C11T29.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T29_den : ℕ := 441
theorem C11T29_den_ok :
    (∀ d ∈ C11T29.R, ∀ e ∈ C11T29.R, (C11T29.Lq d e).den ∣ C11T29_den ∧ (C11T29.Lq' d e).den ∣ C11T29_den) ∧
    (∀ d ∈ C11T29.C, ∀ e ∈ C11T29.C, (C11T29.Pq d e).den ∣ C11T29_den ∧ (C11T29.Pq' d e).den ∣ C11T29_den) := by
  constructor <;> decide +kernel
theorem C11T29_cload_1 : C11T29.cload 1 = ((433 / 441), (-45 / 14)) := by decide +kernel
#print axioms C11T29_ok
#print axioms C11T29_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
