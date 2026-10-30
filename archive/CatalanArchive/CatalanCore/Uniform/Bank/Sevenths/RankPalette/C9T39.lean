import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C9T39
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C9T39_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T39_den) :
    C9T39.Integral p :=
  FibreCert.integral_of_denOk C9T39 C9T39_den p C9T39_den_ok hp

theorem C9T39_palette :
    (∀ d ∈ C9T39.R, C9T39.lf d = poleL 4 0 d ∧ C9T39.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T39.C, C9T39.lf d = poleL 4 0 d ∧ C9T39.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T39_integral
#print axioms C9T39_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
