import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3T38
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T38_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T38_den) :
    C3T38.Integral p :=
  FibreCert.integral_of_denOk C3T38 C3T38_den p C3T38_den_ok hp

theorem C3T38_palette :
    (∀ d ∈ C3T38.R, C3T38.lf d = poleL 5 0 d ∧ C3T38.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T38.C, C3T38.lf d = poleL 5 0 d ∧ C3T38.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T38_integral
#print axioms C3T38_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
