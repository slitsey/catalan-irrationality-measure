import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3T09
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T09_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T09_den) :
    C3T09.Integral p :=
  FibreCert.integral_of_denOk C3T09 C3T09_den p C3T09_den_ok hp

theorem C3T09_palette :
    (∀ d ∈ C3T09.R, C3T09.lf d = poleL 5 0 d ∧ C3T09.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T09.C, C3T09.lf d = poleL 5 0 d ∧ C3T09.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T09_integral
#print axioms C3T09_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
