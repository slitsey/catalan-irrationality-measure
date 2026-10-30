import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3T26
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T26_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T26_den) :
    C3T26.Integral p :=
  FibreCert.integral_of_denOk C3T26 C3T26_den p C3T26_den_ok hp

theorem C3T26_palette :
    (∀ d ∈ C3T26.R, C3T26.lf d = poleL 5 0 d ∧ C3T26.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T26.C, C3T26.lf d = poleL 5 0 d ∧ C3T26.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T26_integral
#print axioms C3T26_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
