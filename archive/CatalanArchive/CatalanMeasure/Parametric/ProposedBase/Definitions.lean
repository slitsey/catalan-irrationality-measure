module
public import CatalanMeasure.Parametric.GoodPrimes
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open OAI.InternalCatalan
open scoped BigOperators
set_option maxRecDepth 4000
instance certificatePrime : Fact (Nat.Prime 1009) := ⟨by decide⟩
def filteredMomentRat (i k : ℕ) : ℚ :=
  ∑ v ∈ Finset.range 8, ((-1 : ℚ)^v * (7 : ℕ).choose v) * momentRat i (15+k+v)
def filteredZetaRat (i k : ℕ) : ℚ :=
  ∑ v ∈ Finset.range 8, ((-1 : ℚ)^v * (7 : ℕ).choose v) * zetaRat i (15+k+v)
end CatalanMeasure.Parametric.ProposedBase
