import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3T10
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T10_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T10_den) :
    C3T10.Integral p :=
  FibreCert.integral_of_denOk C3T10 C3T10_den p C3T10_den_ok hp

theorem C3T10_palette :
    (∀ d ∈ C3T10.R, C3T10.lf d = poleL 5 1 d ∧ C3T10.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T10.C, C3T10.lf d = poleL 5 1 d ∧ C3T10.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T10_integral
#print axioms C3T10_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
