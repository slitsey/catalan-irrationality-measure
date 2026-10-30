import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C5T25
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C5T25_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T25_den) :
    C5T25.Integral p :=
  FibreCert.integral_of_denOk C5T25 C5T25_den p C5T25_den_ok hp

theorem C5T25_palette :
    (∀ d ∈ C5T25.R, C5T25.lf d = poleL 3 0 d ∧ C5T25.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T25.C, C5T25.lf d = poleL 3 0 d ∧ C5T25.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T25_integral
#print axioms C5T25_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
