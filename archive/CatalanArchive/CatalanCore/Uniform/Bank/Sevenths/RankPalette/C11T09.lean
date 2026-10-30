import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C11T09
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C11T09_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T09_den) :
    C11T09.Integral p :=
  FibreCert.integral_of_denOk C11T09 C11T09_den p C11T09_den_ok hp

theorem C11T09_palette :
    (∀ d ∈ C11T09.R, C11T09.lf d = poleL 2 0 d ∧ C11T09.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T09.C, C11T09.lf d = poleL 2 0 d ∧ C11T09.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T09_integral
#print axioms C11T09_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
