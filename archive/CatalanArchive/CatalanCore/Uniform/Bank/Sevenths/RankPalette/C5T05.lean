import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C5T05
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C5T05_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T05_den) :
    C5T05.Integral p :=
  FibreCert.integral_of_denOk C5T05 C5T05_den p C5T05_den_ok hp

theorem C5T05_palette :
    (∀ d ∈ C5T05.R, C5T05.lf d = poleL 3 1 d ∧ C5T05.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T05.C, C5T05.lf d = poleL 3 1 d ∧ C5T05.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T05_integral
#print axioms C5T05_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
