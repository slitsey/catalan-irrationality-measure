import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C11T03
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C11T03_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T03_den) :
    C11T03.Integral p :=
  FibreCert.integral_of_denOk C11T03 C11T03_den p C11T03_den_ok hp

theorem C11T03_palette :
    (∀ d ∈ C11T03.R, C11T03.lf d = poleL 2 1 d ∧ C11T03.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T03.C, C11T03.lf d = poleL 2 1 d ∧ C11T03.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T03_integral
#print axioms C11T03_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
