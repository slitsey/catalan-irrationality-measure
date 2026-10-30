import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 74ecfff7e9b18121f775978db0471fdd359634c024605b8d50e3a28628f7e504, root class 1. -/
def C1T15 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | 2 => (-51 / 8) | 3 => (-781 / 120) | 4 => (-8681 / 1320) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | 2 => (-3105 / 64) | 3 => (-233387 / 4800) | 4 => (-28262327 / 580800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-443771109714841 / 281927549562120) | 4, 1 => (-1952653213553 / 10068841055790) | 4, 2 => (-21785553505433 / 211445662171590) | 4, 3 => (-4992533821 / 71193825647) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (443771109714841 / 281927549562120) | 4, 1 => (1952653213553 / 10068841055790) | 4, 2 => (21785553505433 / 211445662171590) | 4, 3 => (4992533821 / 71193825647) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C1T15_ok : C1T15.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T15_den : ℕ := 845782648686360
theorem C1T15_den_ok :
    (∀ d ∈ C1T15.R, ∀ e ∈ C1T15.R, (C1T15.Lq d e).den ∣ C1T15_den ∧ (C1T15.Lq' d e).den ∣ C1T15_den) ∧
    (∀ d ∈ C1T15.C, ∀ e ∈ C1T15.C, (C1T15.Pq d e).den ∣ C1T15_den ∧ (C1T15.Pq' d e).den ∣ C1T15_den) := by
  constructor <;> decide +kernel
theorem C1T15_rload_4 : C1T15.rload 4 = ((-796007066211827 / 845782648686360), (-2424410564966207 / 563855099124240)) := by decide +kernel
#print axioms C1T15_ok
#print axioms C1T15_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
