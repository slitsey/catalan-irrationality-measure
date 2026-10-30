import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C11T25
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C11T25_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T25_den) :
    C11T25.Integral p :=
  FibreCert.integral_of_denOk C11T25 C11T25_den p C11T25_den_ok hp

theorem C11T25_palette :
    (∀ d ∈ C11T25.R, C11T25.lf d = poleL 2 0 d ∧ C11T25.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T25.C, C11T25.lf d = poleL 2 0 d ∧ C11T25.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T25_integral
#print axioms C11T25_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
