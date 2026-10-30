import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C9T13
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C9T13_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T13_den) :
    C9T13.Integral p :=
  FibreCert.integral_of_denOk C9T13 C9T13_den p C9T13_den_ok hp

theorem C9T13_palette :
    (∀ d ∈ C9T13.R, C9T13.lf d = poleL 4 0 d ∧ C9T13.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T13.C, C9T13.lf d = poleL 4 0 d ∧ C9T13.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T13_integral
#print axioms C9T13_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
