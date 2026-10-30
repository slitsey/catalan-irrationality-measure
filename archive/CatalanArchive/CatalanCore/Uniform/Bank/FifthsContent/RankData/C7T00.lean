import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type f591dfad93bc7da41ee380657a9a7c3878f501783599293d23384f04941a87c9, prime class 7 mod 10. -/
def C7T00 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | 2 => (-19 / 24) | 3 => (-263 / 312) | 4 => (-815 / 936) | 5 => (-95597 / 107640) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | 2 => (-1105 / 576) | 3 => (-63443 / 32448) | 4 => (-1725805 / 876096) | 5 => (-22907876341 / 11586369600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (-271610569878630481873 / 560856855301824979750) | 1, 1 => 1 | 1, 5 => (-4745143271765846966633 / 29164556475694898947000) | 2, 2 => 1 | 2, 5 => (-1057558722443375926993 / 10936708678385587105125) | 3, 3 => 1 | 3, 5 => (-38514626885803144509 / 560856855301824979750) | 4, 4 => 1 | 4, 5 => (-14922553118611922064 / 280428427650912489875) | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (271610569878630481873 / 560856855301824979750) | 1, 1 => 1 | 1, 5 => (4745143271765846966633 / 29164556475694898947000) | 2, 2 => 1 | 2, 5 => (1057558722443375926993 / 10936708678385587105125) | 3, 3 => 1 | 3, 5 => (38514626885803144509 / 560856855301824979750) | 4, 4 => 1 | 4, 5 => (14922553118611922064 / 280428427650912489875) | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := {5}

theorem C7T00_ok : C7T00.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T00_den : ℕ := 87493669427084696841000
theorem C7T00_den_ok :
    (∀ d ∈ C7T00.R, ∀ e ∈ C7T00.R, (C7T00.Lq d e).den ∣ C7T00_den ∧ (C7T00.Lq' d e).den ∣ C7T00_den) ∧
    (∀ d ∈ C7T00.C, ∀ e ∈ C7T00.C, (C7T00.Pq d e).den ∣ C7T00_den ∧ (C7T00.Pq' d e).den ∣ C7T00_den) := by
  constructor <;> decide +kernel
theorem C7T00_cload_5 : C7T00.cload 5 = ((511408807129634048939 / 3804072583786291167000), (-2687071438989742687947 / 4486854842414599838000)) := by decide +kernel
#print axioms C7T00_ok
#print axioms C7T00_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
