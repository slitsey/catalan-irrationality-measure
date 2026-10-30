import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13T00
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C13T00_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T00_den) :
    C13T00.Integral p :=
  FibreCert.integral_of_denOk C13T00 C13T00_den p C13T00_den_ok hp

theorem C13T00_palette :
    (∀ d ∈ C13T00.R, C13T00.lf d = poleL 6 0 d ∧ C13T00.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T00.C, C13T00.lf d = poleL 6 0 d ∧ C13T00.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T00_integral
#print axioms C13T00_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
