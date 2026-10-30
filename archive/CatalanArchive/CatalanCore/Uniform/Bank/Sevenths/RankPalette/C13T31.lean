import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13T31
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C13T31_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T31_den) :
    C13T31.Integral p :=
  FibreCert.integral_of_denOk C13T31 C13T31_den p C13T31_den_ok hp

theorem C13T31_palette :
    (∀ d ∈ C13T31.R, C13T31.lf d = poleL 6 1 d ∧ C13T31.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T31.C, C13T31.lf d = poleL 6 1 d ∧ C13T31.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T31_integral
#print axioms C13T31_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
