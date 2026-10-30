import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type ef9c636e9adb8185200b5b79775504473025e0c64ce6ef3946dbb3da28f99ccb, prime class 1 mod 10. -/
def C1T01 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-4) | 2 => (-13 / 3) | 3 => (-49 / 11) | 4 => (-795 / 176) | 5 => (-84179 / 18480) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24) | 2 => (-220 / 9) | 3 => (-8908 / 363) | 4 => (-2283715 / 92928) | 5 => (-8398352209 / 341510400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (-450593551014720617697 / 485931005227583377000) | 5, 1 => (-20927458798873593801 / 138837430065023822000) | 5, 2 => (-39680590654637121011 / 485931005227583377000) | 5, 3 => (-9889201979884424409 / 176702183719121228000) | 5, 4 => (-235037733753831054 / 5521943241222538375) | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (450593551014720617697 / 485931005227583377000) | 5, 1 => (20927458798873593801 / 138837430065023822000) | 5, 2 => (39680590654637121011 / 485931005227583377000) | 5, 3 => (9889201979884424409 / 176702183719121228000) | 5, 4 => (235037733753831054 / 5521943241222538375) | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := {5}
  kc := ∅

theorem C1T01_ok : C1T01.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T01_den : ℕ := 1943724020910333508000
theorem C1T01_den_ok :
    (∀ d ∈ C1T01.R, ∀ e ∈ C1T01.R, (C1T01.Lq d e).den ∣ C1T01_den ∧ (C1T01.Lq' d e).den ∣ C1T01_den) ∧
    (∀ d ∈ C1T01.C, ∀ e ∈ C1T01.C, (C1T01.Pq d e).den ∣ C1T01_den ∧ (C1T01.Pq' d e).den ∣ C1T01_den) := by
  constructor <;> decide +kernel
theorem C1T01_rload_5 : C1T01.rload 5 = ((-501871473011404959553 / 1943724020910333508000), (-876560127401660361767 / 277674860130047644000)) := by decide +kernel
#print axioms C1T01_ok
#print axioms C1T01_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
