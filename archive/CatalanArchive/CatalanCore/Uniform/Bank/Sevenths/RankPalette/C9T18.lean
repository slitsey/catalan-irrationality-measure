import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C9T18
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C9T18_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T18_den) :
    C9T18.Integral p :=
  FibreCert.integral_of_denOk C9T18 C9T18_den p C9T18_den_ok hp

theorem C9T18_palette :
    (∀ d ∈ C9T18.R, C9T18.lf d = poleL 4 1 d ∧ C9T18.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T18.C, C9T18.lf d = poleL 4 1 d ∧ C9T18.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T18_integral
#print axioms C9T18_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
