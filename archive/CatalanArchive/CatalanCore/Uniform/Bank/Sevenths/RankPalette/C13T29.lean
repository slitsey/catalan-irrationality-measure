import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13T29
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C13T29_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T29_den) :
    C13T29.Integral p :=
  FibreCert.integral_of_denOk C13T29 C13T29_den p C13T29_den_ok hp

theorem C13T29_palette :
    (∀ d ∈ C13T29.R, C13T29.lf d = poleL 6 0 d ∧ C13T29.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T29.C, C13T29.lf d = poleL 6 0 d ∧ C13T29.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T29_integral
#print axioms C13T29_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
