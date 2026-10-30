import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C1T09
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C1T09_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T09_den) :
    C1T09.Integral p :=
  FibreCert.integral_of_denOk C1T09 C1T09_den p C1T09_den_ok hp

theorem C1T09_palette :
    (∀ d ∈ C1T09.R, C1T09.lf d = poleL 1 0 d ∧ C1T09.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T09.C, C1T09.lf d = poleL 1 0 d ∧ C1T09.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T09_integral
#print axioms C1T09_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
