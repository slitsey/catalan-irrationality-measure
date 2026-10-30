import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C9T25
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C9T25_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T25_den) :
    C9T25.Integral p :=
  FibreCert.integral_of_denOk C9T25 C9T25_den p C9T25_den_ok hp

theorem C9T25_palette :
    (∀ d ∈ C9T25.R, C9T25.lf d = poleL 4 1 d ∧ C9T25.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T25.C, C9T25.lf d = poleL 4 1 d ∧ C9T25.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T25_integral
#print axioms C9T25_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
