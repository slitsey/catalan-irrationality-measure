import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C11T08
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C11T08_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T08_den) :
    C11T08.Integral p :=
  FibreCert.integral_of_denOk C11T08 C11T08_den p C11T08_den_ok hp

theorem C11T08_palette :
    (∀ d ∈ C11T08.R, C11T08.lf d = poleL 2 0 d ∧ C11T08.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T08.C, C11T08.lf d = poleL 2 0 d ∧ C11T08.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T08_integral
#print axioms C11T08_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
