import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C5T38
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C5T38_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T38_den) :
    C5T38.Integral p :=
  FibreCert.integral_of_denOk C5T38 C5T38_den p C5T38_den_ok hp

theorem C5T38_palette :
    (∀ d ∈ C5T38.R, C5T38.lf d = poleL 3 0 d ∧ C5T38.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T38.C, C5T38.lf d = poleL 3 0 d ∧ C5T38.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T38_integral
#print axioms C5T38_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
