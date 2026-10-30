import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13T35
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C13T35_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T35_den) :
    C13T35.Integral p :=
  FibreCert.integral_of_denOk C13T35 C13T35_den p C13T35_den_ok hp

theorem C13T35_palette :
    (∀ d ∈ C13T35.R, C13T35.lf d = poleL 6 0 d ∧ C13T35.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T35.C, C13T35.lf d = poleL 6 0 d ∧ C13T35.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T35_integral
#print axioms C13T35_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
