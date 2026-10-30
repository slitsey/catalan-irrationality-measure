import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type ed131775179d383d1d416c0b31b2a14e94cd896f09ed7bb7cb2d3107b69c2f64, prime class 1 mod 10. -/
def C1T02 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => (-5) | 1 => (-29 / 6) | 2 => (-158 / 33) | 3 => (-839 / 176) | 4 => (-17575 / 3696) | 5 => (-1140527 / 240240) | _ => 0
  ee := fun d => match d with | 0 => (-25) | 1 => (-889 / 36) | 2 => (-26845 / 1089) | 3 => (-2289523 / 92928) | 4 => (-336480505 / 13660416) | 5 => (-1421455963321 / 57715257600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (-89689938760226751410274477 / 44611066875352753936703452000) | 1, 1 => 1 | 1, 5 => (-22058589834857291121773139 / 25827459769941068068617788000) | 2, 2 => 1 | 2, 5 => (-47818200843803620959874027 / 89222133750705507873406904000) | 3, 3 => 1 | 3, 5 => (-77595385340386074539229 / 199156548550681937217426125) | 4, 4 => 1 | 4, 5 => (-121822944189965677739061 / 398313097101363874434852250) | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (89689938760226751410274477 / 44611066875352753936703452000) | 1, 1 => 1 | 1, 5 => (22058589834857291121773139 / 25827459769941068068617788000) | 2, 2 => 1 | 2, 5 => (47818200843803620959874027 / 89222133750705507873406904000) | 3, 3 => 1 | 3, 5 => (77595385340386074539229 / 199156548550681937217426125) | 4, 4 => 1 | 4, 5 => (121822944189965677739061 / 398313097101363874434852250) | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := {5}

theorem C1T02_ok : C1T02.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T02_den : ℕ := 981443471257760586607475944000
theorem C1T02_den_ok :
    (∀ d ∈ C1T02.R, ∀ e ∈ C1T02.R, (C1T02.Lq d e).den ∣ C1T02_den ∧ (C1T02.Lq' d e).den ∣ C1T02_den) ∧
    (∀ d ∈ C1T02.C, ∀ e ∈ C1T02.C, (C1T02.Pq d e).den ∣ C1T02_den ∧ (C1T02.Pq' d e).den ∣ C1T02_den) := by
  constructor <;> decide +kernel
theorem C1T02_cload_5 : C1T02.cload 5 = ((977423504188587683177985545111 / 981443471257760586607475944000), (-4639666246744549323497788770227 / 981443471257760586607475944000)) := by decide +kernel
#print axioms C1T02_ok
#print axioms C1T02_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
