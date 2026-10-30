import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C1T31
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C1T31_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T31_den) :
    C1T31.Integral p :=
  FibreCert.integral_of_denOk C1T31 C1T31_den p C1T31_den_ok hp

theorem C1T31_palette :
    (∀ d ∈ C1T31.R, C1T31.lf d = poleL 1 0 d ∧ C1T31.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T31.C, C1T31.lf d = poleL 1 0 d ∧ C1T31.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T31_integral
#print axioms C1T31_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
