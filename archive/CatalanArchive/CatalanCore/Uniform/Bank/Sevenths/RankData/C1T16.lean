import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d66f4d6b85a191545703c60eb56aa6e1eb39e3564b29b74a985babeff45f219d, root class 1. -/
def C1T16 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | 2 => (-51 / 8) | 3 => (-781 / 120) | 4 => (-8681 / 1320) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | 2 => (-3105 / 64) | 3 => (-233387 / 4800) | 4 => (-28262327 / 580800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-443771109714841 / 281927549562120) | 1, 1 => 1 | 1, 4 => (-1952653213553 / 10068841055790) | 2, 2 => 1 | 2, 4 => (-21785553505433 / 211445662171590) | 3, 3 => 1 | 3, 4 => (-4992533821 / 71193825647) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (443771109714841 / 281927549562120) | 1, 1 => 1 | 1, 4 => (1952653213553 / 10068841055790) | 2, 2 => 1 | 2, 4 => (21785553505433 / 211445662171590) | 3, 3 => 1 | 3, 4 => (4992533821 / 71193825647) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C1T16_ok : C1T16.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T16_den : ℕ := 845782648686360
theorem C1T16_den_ok :
    (∀ d ∈ C1T16.R, ∀ e ∈ C1T16.R, (C1T16.Lq d e).den ∣ C1T16_den ∧ (C1T16.Lq' d e).den ∣ C1T16_den) ∧
    (∀ d ∈ C1T16.C, ∀ e ∈ C1T16.C, (C1T16.Pq d e).den ∣ C1T16_den ∧ (C1T16.Pq' d e).den ∣ C1T16_den) := by
  constructor <;> decide +kernel
theorem C1T16_cload_4 : C1T16.cload 4 = ((-796007066211827 / 845782648686360), (-2424410564966207 / 563855099124240)) := by decide +kernel
#print axioms C1T16_ok
#print axioms C1T16_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
