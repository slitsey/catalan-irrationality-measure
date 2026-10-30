import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C9T10
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C9T10_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T10_den) :
    C9T10.Integral p :=
  FibreCert.integral_of_denOk C9T10 C9T10_den p C9T10_den_ok hp

theorem C9T10_palette :
    (∀ d ∈ C9T10.R, C9T10.lf d = poleL 4 1 d ∧ C9T10.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T10.C, C9T10.lf d = poleL 4 1 d ∧ C9T10.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T10_integral
#print axioms C9T10_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
