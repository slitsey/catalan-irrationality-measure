import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 328d4b0acc1ebe844e70425581fbf63b045899b4d90ba10019d03b3e085ce472, prime class 1 mod 10. -/
def C1T00 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-4) | 2 => (-13 / 3) | 3 => (-49 / 11) | 4 => (-795 / 176) | 5 => (-84179 / 18480) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24) | 2 => (-220 / 9) | 3 => (-8908 / 363) | 4 => (-2283715 / 92928) | 5 => (-8398352209 / 341510400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (-450593551014720617697 / 485931005227583377000) | 1, 1 => 1 | 1, 5 => (-20927458798873593801 / 138837430065023822000) | 2, 2 => 1 | 2, 5 => (-39680590654637121011 / 485931005227583377000) | 3, 3 => 1 | 3, 5 => (-9889201979884424409 / 176702183719121228000) | 4, 4 => 1 | 4, 5 => (-235037733753831054 / 5521943241222538375) | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (450593551014720617697 / 485931005227583377000) | 1, 1 => 1 | 1, 5 => (20927458798873593801 / 138837430065023822000) | 2, 2 => 1 | 2, 5 => (39680590654637121011 / 485931005227583377000) | 3, 3 => 1 | 3, 5 => (9889201979884424409 / 176702183719121228000) | 4, 4 => 1 | 4, 5 => (235037733753831054 / 5521943241222538375) | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := {5}

theorem C1T00_ok : C1T00.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T00_den : ℕ := 1943724020910333508000
theorem C1T00_den_ok :
    (∀ d ∈ C1T00.R, ∀ e ∈ C1T00.R, (C1T00.Lq d e).den ∣ C1T00_den ∧ (C1T00.Lq' d e).den ∣ C1T00_den) ∧
    (∀ d ∈ C1T00.C, ∀ e ∈ C1T00.C, (C1T00.Pq d e).den ∣ C1T00_den ∧ (C1T00.Pq' d e).den ∣ C1T00_den) := by
  constructor <;> decide +kernel
theorem C1T00_cload_5 : C1T00.cload 5 = ((-501871473011404959553 / 1943724020910333508000), (-876560127401660361767 / 277674860130047644000)) := by decide +kernel
#print axioms C1T00_ok
#print axioms C1T00_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
