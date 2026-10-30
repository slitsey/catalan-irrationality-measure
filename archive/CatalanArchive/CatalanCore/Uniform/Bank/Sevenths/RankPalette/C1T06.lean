import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C1T06
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C1T06_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T06_den) :
    C1T06.Integral p :=
  FibreCert.integral_of_denOk C1T06 C1T06_den p C1T06_den_ok hp

theorem C1T06_palette :
    (∀ d ∈ C1T06.R, C1T06.lf d = poleL 1 1 d ∧ C1T06.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T06.C, C1T06.lf d = poleL 1 1 d ∧ C1T06.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T06_integral
#print axioms C1T06_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
