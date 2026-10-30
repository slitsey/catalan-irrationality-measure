import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13T07
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C13T07_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T07_den) :
    C13T07.Integral p :=
  FibreCert.integral_of_denOk C13T07 C13T07_den p C13T07_den_ok hp

theorem C13T07_palette :
    (∀ d ∈ C13T07.R, C13T07.lf d = poleL 6 0 d ∧ C13T07.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T07.C, C13T07.lf d = poleL 6 0 d ∧ C13T07.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T07_integral
#print axioms C13T07_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
