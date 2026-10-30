import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C11T18
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C11T18_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T18_den) :
    C11T18.Integral p :=
  FibreCert.integral_of_denOk C11T18 C11T18_den p C11T18_den_ok hp

theorem C11T18_palette :
    (∀ d ∈ C11T18.R, C11T18.lf d = poleL 2 1 d ∧ C11T18.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T18.C, C11T18.lf d = poleL 2 1 d ∧ C11T18.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T18_integral
#print axioms C11T18_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
