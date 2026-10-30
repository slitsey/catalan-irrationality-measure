import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C11T27
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C11T27_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T27_den) :
    C11T27.Integral p :=
  FibreCert.integral_of_denOk C11T27 C11T27_den p C11T27_den_ok hp

theorem C11T27_palette :
    (∀ d ∈ C11T27.R, C11T27.lf d = poleL 2 0 d ∧ C11T27.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T27.C, C11T27.lf d = poleL 2 0 d ∧ C11T27.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T27_integral
#print axioms C11T27_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
