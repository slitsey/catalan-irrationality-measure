import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13T19
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C13T19_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T19_den) :
    C13T19.Integral p :=
  FibreCert.integral_of_denOk C13T19 C13T19_den p C13T19_den_ok hp

theorem C13T19_palette :
    (∀ d ∈ C13T19.R, C13T19.lf d = poleL 6 1 d ∧ C13T19.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T19.C, C13T19.lf d = poleL 6 1 d ∧ C13T19.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T19_integral
#print axioms C13T19_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
