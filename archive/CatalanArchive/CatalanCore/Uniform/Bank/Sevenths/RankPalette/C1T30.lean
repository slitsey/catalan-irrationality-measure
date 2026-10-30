import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C1T30
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C1T30_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T30_den) :
    C1T30.Integral p :=
  FibreCert.integral_of_denOk C1T30 C1T30_den p C1T30_den_ok hp

theorem C1T30_palette :
    (∀ d ∈ C1T30.R, C1T30.lf d = poleL 1 1 d ∧ C1T30.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T30.C, C1T30.lf d = poleL 1 1 d ∧ C1T30.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T30_integral
#print axioms C1T30_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
