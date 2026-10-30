import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C5T30
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C5T30_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T30_den) :
    C5T30.Integral p :=
  FibreCert.integral_of_denOk C5T30 C5T30_den p C5T30_den_ok hp

theorem C5T30_palette :
    (∀ d ∈ C5T30.R, C5T30.lf d = poleL 3 1 d ∧ C5T30.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T30.C, C5T30.lf d = poleL 3 1 d ∧ C5T30.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T30_integral
#print axioms C5T30_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
