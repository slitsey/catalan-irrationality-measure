import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 041bcd71b6461b92a7ed2b7d02dcd1e763f8a4e5311b38e725b2dda823f39460, root class 11. -/
def C11T24 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 2) | 1 => (-59 / 18) | 2 => (-463 / 144) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | 1 => (-3841 / 324) | 2 => (-244609 / 20736) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-31237 / 2709288) | 1, 1 => 1 | 1, 2 => (-761 / 150516) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (31237 / 2709288) | 1, 1 => 1 | 1, 2 => (761 / 150516) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C11T24_ok : C11T24.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T24_den : ℕ := 2709288
theorem C11T24_den_ok :
    (∀ d ∈ C11T24.R, ∀ e ∈ C11T24.R, (C11T24.Lq d e).den ∣ C11T24_den ∧ (C11T24.Lq' d e).den ∣ C11T24_den) ∧
    (∀ d ∈ C11T24.C, ∀ e ∈ C11T24.C, (C11T24.Pq d e).den ∣ C11T24_den ∧ (C11T24.Pq' d e).den ∣ C11T24_den) := by
  constructor <;> decide +kernel
theorem C11T24_cload_2 : C11T24.cload 2 = ((2664353 / 2709288), (-950765 / 301032)) := by decide +kernel
#print axioms C11T24_ok
#print axioms C11T24_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
