import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C11T32
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C11T32_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T32_den) :
    C11T32.Integral p :=
  FibreCert.integral_of_denOk C11T32 C11T32_den p C11T32_den_ok hp

theorem C11T32_palette :
    (∀ d ∈ C11T32.R, C11T32.lf d = poleL 2 1 d ∧ C11T32.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T32.C, C11T32.lf d = poleL 2 1 d ∧ C11T32.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T32_integral
#print axioms C11T32_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
