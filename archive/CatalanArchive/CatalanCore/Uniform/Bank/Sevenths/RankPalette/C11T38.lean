import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C11T38
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C11T38_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T38_den) :
    C11T38.Integral p :=
  FibreCert.integral_of_denOk C11T38 C11T38_den p C11T38_den_ok hp

theorem C11T38_palette :
    (∀ d ∈ C11T38.R, C11T38.lf d = poleL 2 0 d ∧ C11T38.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T38.C, C11T38.lf d = poleL 2 0 d ∧ C11T38.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T38_integral
#print axioms C11T38_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
