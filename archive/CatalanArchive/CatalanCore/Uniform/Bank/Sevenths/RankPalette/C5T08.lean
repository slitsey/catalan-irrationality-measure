import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C5T08
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C5T08_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T08_den) :
    C5T08.Integral p :=
  FibreCert.integral_of_denOk C5T08 C5T08_den p C5T08_den_ok hp

theorem C5T08_palette :
    (∀ d ∈ C5T08.R, C5T08.lf d = poleL 3 0 d ∧ C5T08.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T08.C, C5T08.lf d = poleL 3 0 d ∧ C5T08.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T08_integral
#print axioms C5T08_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
