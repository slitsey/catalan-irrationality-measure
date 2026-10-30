import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13T11
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C13T11_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T11_den) :
    C13T11.Integral p :=
  FibreCert.integral_of_denOk C13T11 C13T11_den p C13T11_den_ok hp

theorem C13T11_palette :
    (∀ d ∈ C13T11.R, C13T11.lf d = poleL 6 0 d ∧ C13T11.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T11.C, C13T11.lf d = poleL 6 0 d ∧ C13T11.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T11_integral
#print axioms C13T11_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
