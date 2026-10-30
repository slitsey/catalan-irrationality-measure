import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C9T12
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C9T12_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T12_den) :
    C9T12.Integral p :=
  FibreCert.integral_of_denOk C9T12 C9T12_den p C9T12_den_ok hp

theorem C9T12_palette :
    (∀ d ∈ C9T12.R, C9T12.lf d = poleL 4 1 d ∧ C9T12.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T12.C, C9T12.lf d = poleL 4 1 d ∧ C9T12.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T12_integral
#print axioms C9T12_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
