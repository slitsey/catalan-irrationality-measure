import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C9T01
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C9T01_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T01_den) :
    C9T01.Integral p :=
  FibreCert.integral_of_denOk C9T01 C9T01_den p C9T01_den_ok hp

theorem C9T01_palette :
    (∀ d ∈ C9T01.R, C9T01.lf d = poleL 4 0 d ∧ C9T01.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T01.C, C9T01.lf d = poleL 4 0 d ∧ C9T01.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T01_integral
#print axioms C9T01_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
