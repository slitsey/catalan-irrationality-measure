import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C5T27
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C5T27_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T27_den) :
    C5T27.Integral p :=
  FibreCert.integral_of_denOk C5T27 C5T27_den p C5T27_den_ok hp

theorem C5T27_palette :
    (∀ d ∈ C5T27.R, C5T27.lf d = poleL 3 0 d ∧ C5T27.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T27.C, C5T27.lf d = poleL 3 0 d ∧ C5T27.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T27_integral
#print axioms C5T27_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
