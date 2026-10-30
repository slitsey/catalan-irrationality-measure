import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C11T39
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C11T39_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T39_den) :
    C11T39.Integral p :=
  FibreCert.integral_of_denOk C11T39 C11T39_den p C11T39_den_ok hp

theorem C11T39_palette :
    (∀ d ∈ C11T39.R, C11T39.lf d = poleL 2 0 d ∧ C11T39.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T39.C, C11T39.lf d = poleL 2 0 d ∧ C11T39.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T39_integral
#print axioms C11T39_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
