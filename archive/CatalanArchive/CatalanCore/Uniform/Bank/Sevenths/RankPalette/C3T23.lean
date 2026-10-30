import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3T23
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T23_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T23_den) :
    C3T23.Integral p :=
  FibreCert.integral_of_denOk C3T23 C3T23_den p C3T23_den_ok hp

theorem C3T23_palette :
    (∀ d ∈ C3T23.R, C3T23.lf d = poleL 5 0 d ∧ C3T23.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T23.C, C3T23.lf d = poleL 5 0 d ∧ C3T23.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T23_integral
#print axioms C3T23_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
