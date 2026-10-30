import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3T16
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T16_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T16_den) :
    C3T16.Integral p :=
  FibreCert.integral_of_denOk C3T16 C3T16_den p C3T16_den_ok hp

theorem C3T16_palette :
    (∀ d ∈ C3T16.R, C3T16.lf d = poleL 5 1 d ∧ C3T16.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T16.C, C3T16.lf d = poleL 5 1 d ∧ C3T16.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T16_integral
#print axioms C3T16_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
