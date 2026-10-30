import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C9T24
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C9T24_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T24_den) :
    C9T24.Integral p :=
  FibreCert.integral_of_denOk C9T24 C9T24_den p C9T24_den_ok hp

theorem C9T24_palette :
    (∀ d ∈ C9T24.R, C9T24.lf d = poleL 4 1 d ∧ C9T24.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T24.C, C9T24.lf d = poleL 4 1 d ∧ C9T24.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T24_integral
#print axioms C9T24_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
