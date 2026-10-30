import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 6d9b7cf9a9a099fa93a10ba346058dd90c5c245007aa332ff6d340577d718545, prime class 7 mod 10. -/
def C7T01 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | 2 => (-19 / 24) | 3 => (-263 / 312) | 4 => (-815 / 936) | 5 => (-95597 / 107640) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | 2 => (-1105 / 576) | 3 => (-63443 / 32448) | 4 => (-1725805 / 876096) | 5 => (-22907876341 / 11586369600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (-271610569878630481873 / 560856855301824979750) | 5, 1 => (-4745143271765846966633 / 29164556475694898947000) | 5, 2 => (-1057558722443375926993 / 10936708678385587105125) | 5, 3 => (-38514626885803144509 / 560856855301824979750) | 5, 4 => (-14922553118611922064 / 280428427650912489875) | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (271610569878630481873 / 560856855301824979750) | 5, 1 => (4745143271765846966633 / 29164556475694898947000) | 5, 2 => (1057558722443375926993 / 10936708678385587105125) | 5, 3 => (38514626885803144509 / 560856855301824979750) | 5, 4 => (14922553118611922064 / 280428427650912489875) | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := {5}
  kc := ∅

theorem C7T01_ok : C7T01.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T01_den : ℕ := 87493669427084696841000
theorem C7T01_den_ok :
    (∀ d ∈ C7T01.R, ∀ e ∈ C7T01.R, (C7T01.Lq d e).den ∣ C7T01_den ∧ (C7T01.Lq' d e).den ∣ C7T01_den) ∧
    (∀ d ∈ C7T01.C, ∀ e ∈ C7T01.C, (C7T01.Pq d e).den ∣ C7T01_den ∧ (C7T01.Pq' d e).den ∣ C7T01_den) := by
  constructor <;> decide +kernel
theorem C7T01_rload_5 : C7T01.rload 5 = ((511408807129634048939 / 3804072583786291167000), (-2687071438989742687947 / 4486854842414599838000)) := by decide +kernel
#print axioms C7T01_ok
#print axioms C7T01_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
