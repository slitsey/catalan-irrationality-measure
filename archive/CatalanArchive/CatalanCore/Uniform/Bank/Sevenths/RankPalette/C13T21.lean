import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13T21
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C13T21_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T21_den) :
    C13T21.Integral p :=
  FibreCert.integral_of_denOk C13T21 C13T21_den p C13T21_den_ok hp

theorem C13T21_palette :
    (∀ d ∈ C13T21.R, C13T21.lf d = poleL 6 0 d ∧ C13T21.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T21.C, C13T21.lf d = poleL 6 0 d ∧ C13T21.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T21_integral
#print axioms C13T21_palette
end CatalanCore.Uniform.Bank.Sevenths.RankData
