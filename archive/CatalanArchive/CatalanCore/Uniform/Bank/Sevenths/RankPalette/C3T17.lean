import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3T17
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T17_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T17_den) :
    C3T17.Integral p :=
  FibreCert.integral_of_denOk C3T17 C3T17_den p C3T17_den_ok hp

theorem C3T17_palette :
    (∀ d ∈ C3T17.R, C3T17.lf d = poleL 5 0 d ∧ C3T17.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T17.C, C3T17.lf d = poleL 5 0 d ∧ C3T17.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T17_integral
#print axioms C3T17_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
