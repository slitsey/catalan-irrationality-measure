module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRankContent
public import CatalanArchive.CatalanMeasure.Parametric.U6Rank
@[expose] public section

/-!
# From the U6 rank bound to coefficient content (primes in `(4N, 9N/2)`)

On the sixth window `4N < p`, `2p < 9N` the canonical normalizer already has the
full double-pole exponent `40N`, so the rank bound of Lemma U6 gives
`p ^ ((p - 4N - 1) / 2)` dividing every coefficient of the canonical integer
polynomial.
-/

namespace CatalanMeasure.Parametric
open Polynomial Matrix Finset OAI.InternalCatalan
open scoped BigOperators Nat
noncomputable section

/-- The content exponent at a prime in the sixth window. -/
def sixthExponent (N p : ℕ) : ℕ := (p - 4 * N - 1) / 2

/-- The U6 rank bound gives `p^e` dividing every coefficient. -/
theorem twentyMeasureIntPoly_sixth_coeff_dvd {N p : ℕ} [Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (h4 : 4 * N < p) (h9 : 2 * p < 9 * N) :
    ∀ i, (p : ℤ) ^ (sixthExponent N p) ∣ (twentyMeasureIntPoly N).coeff i := by
  have hNpos : 0 < N := by omega
  have hr := u6_canonical_rank (p := p) hNpos h4 h9
  unfold sixthExponent
  exact twentyMeasureIntPoly_coeff_prime_pow_dvd_of_rank hbig (by omega) (by omega)
    (by omega) (by omega)

end
end CatalanMeasure.Parametric
