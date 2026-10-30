import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13T13
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C13T13_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T13_den) :
    C13T13.Integral p :=
  FibreCert.integral_of_denOk C13T13 C13T13_den p C13T13_den_ok hp

theorem C13T13_palette :
    (∀ d ∈ C13T13.R, C13T13.lf d = poleL 6 1 d ∧ C13T13.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T13.C, C13T13.lf d = poleL 6 1 d ∧ C13T13.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T13_integral
#print axioms C13T13_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
