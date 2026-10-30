import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 992b779b90125909b3ec992a2272870fb12d987435590bf162ba4030df9b79b1, prime class 1 mod 10. -/
def C1T03 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-5) | 1 => (-29 / 6) | 2 => (-158 / 33) | 3 => (-839 / 176) | 4 => (-17575 / 3696) | 5 => (-1140527 / 240240) | _ => 0
  ee := fun d => match d with | 0 => (-25) | 1 => (-889 / 36) | 2 => (-26845 / 1089) | 3 => (-2289523 / 92928) | 4 => (-336480505 / 13660416) | 5 => (-1421455963321 / 57715257600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (-89689938760226751410274477 / 44611066875352753936703452000) | 5, 1 => (-22058589834857291121773139 / 25827459769941068068617788000) | 5, 2 => (-47818200843803620959874027 / 89222133750705507873406904000) | 5, 3 => (-77595385340386074539229 / 199156548550681937217426125) | 5, 4 => (-121822944189965677739061 / 398313097101363874434852250) | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (89689938760226751410274477 / 44611066875352753936703452000) | 5, 1 => (22058589834857291121773139 / 25827459769941068068617788000) | 5, 2 => (47818200843803620959874027 / 89222133750705507873406904000) | 5, 3 => (77595385340386074539229 / 199156548550681937217426125) | 5, 4 => (121822944189965677739061 / 398313097101363874434852250) | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := {5}
  kc := ∅

theorem C1T03_ok : C1T03.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T03_den : ℕ := 981443471257760586607475944000
theorem C1T03_den_ok :
    (∀ d ∈ C1T03.R, ∀ e ∈ C1T03.R, (C1T03.Lq d e).den ∣ C1T03_den ∧ (C1T03.Lq' d e).den ∣ C1T03_den) ∧
    (∀ d ∈ C1T03.C, ∀ e ∈ C1T03.C, (C1T03.Pq d e).den ∣ C1T03_den ∧ (C1T03.Pq' d e).den ∣ C1T03_den) := by
  constructor <;> decide +kernel
theorem C1T03_rload_5 : C1T03.rload 5 = ((977423504188587683177985545111 / 981443471257760586607475944000), (-4639666246744549323497788770227 / 981443471257760586607475944000)) := by decide +kernel
#print axioms C1T03_ok
#print axioms C1T03_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
