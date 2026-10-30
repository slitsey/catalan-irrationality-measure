import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3T29
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T29_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T29_den) :
    C3T29.Integral p :=
  FibreCert.integral_of_denOk C3T29 C3T29_den p C3T29_den_ok hp

theorem C3T29_palette :
    (∀ d ∈ C3T29.R, C3T29.lf d = poleL 5 0 d ∧ C3T29.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T29.C, C3T29.lf d = poleL 5 0 d ∧ C3T29.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T29_integral
#print axioms C3T29_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
