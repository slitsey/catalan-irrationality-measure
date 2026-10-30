import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C5T16
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C5T16_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T16_den) :
    C5T16.Integral p :=
  FibreCert.integral_of_denOk C5T16 C5T16_den p C5T16_den_ok hp

theorem C5T16_palette :
    (∀ d ∈ C5T16.R, C5T16.lf d = poleL 3 1 d ∧ C5T16.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T16.C, C5T16.lf d = poleL 3 1 d ∧ C5T16.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T16_integral
#print axioms C5T16_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
