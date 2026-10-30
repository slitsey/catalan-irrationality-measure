import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13T30
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C13T30_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T30_den) :
    C13T30.Integral p :=
  FibreCert.integral_of_denOk C13T30 C13T30_den p C13T30_den_ok hp

theorem C13T30_palette :
    (∀ d ∈ C13T30.R, C13T30.lf d = poleL 6 1 d ∧ C13T30.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T30.C, C13T30.lf d = poleL 6 1 d ∧ C13T30.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T30_integral
#print axioms C13T30_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
