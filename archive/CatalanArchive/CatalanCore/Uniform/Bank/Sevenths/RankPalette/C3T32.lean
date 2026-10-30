import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3T32
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T32_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T32_den) :
    C3T32.Integral p :=
  FibreCert.integral_of_denOk C3T32 C3T32_den p C3T32_den_ok hp

theorem C3T32_palette :
    (∀ d ∈ C3T32.R, C3T32.lf d = poleL 5 0 d ∧ C3T32.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T32.C, C3T32.lf d = poleL 5 0 d ∧ C3T32.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T32_integral
#print axioms C3T32_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
