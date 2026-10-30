import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C9T34
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C9T34_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T34_den) :
    C9T34.Integral p :=
  FibreCert.integral_of_denOk C9T34 C9T34_den p C9T34_den_ok hp

theorem C9T34_palette :
    (∀ d ∈ C9T34.R, C9T34.lf d = poleL 4 0 d ∧ C9T34.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T34.C, C9T34.lf d = poleL 4 0 d ∧ C9T34.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T34_integral
#print axioms C9T34_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
