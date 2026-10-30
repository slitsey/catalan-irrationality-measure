import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3T07
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T07_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T07_den) :
    C3T07.Integral p :=
  FibreCert.integral_of_denOk C3T07 C3T07_den p C3T07_den_ok hp

theorem C3T07_palette :
    (∀ d ∈ C3T07.R, C3T07.lf d = poleL 5 0 d ∧ C3T07.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T07.C, C3T07.lf d = poleL 5 0 d ∧ C3T07.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T07_integral
#print axioms C3T07_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
