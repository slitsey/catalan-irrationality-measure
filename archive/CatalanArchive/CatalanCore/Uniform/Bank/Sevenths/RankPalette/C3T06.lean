import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3T06
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T06_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T06_den) :
    C3T06.Integral p :=
  FibreCert.integral_of_denOk C3T06 C3T06_den p C3T06_den_ok hp

theorem C3T06_palette :
    (∀ d ∈ C3T06.R, C3T06.lf d = poleL 5 1 d ∧ C3T06.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T06.C, C3T06.lf d = poleL 5 1 d ∧ C3T06.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T06_integral
#print axioms C3T06_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
