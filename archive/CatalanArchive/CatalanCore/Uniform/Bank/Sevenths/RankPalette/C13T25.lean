import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13T25
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C13T25_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T25_den) :
    C13T25.Integral p :=
  FibreCert.integral_of_denOk C13T25 C13T25_den p C13T25_den_ok hp

theorem C13T25_palette :
    (∀ d ∈ C13T25.R, C13T25.lf d = poleL 6 1 d ∧ C13T25.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T25.C, C13T25.lf d = poleL 6 1 d ∧ C13T25.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T25_integral
#print axioms C13T25_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
