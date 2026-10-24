module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceLaurent

/-! Evaluation of the actual reversed finite source under a unit variable.
This is the denominator-clearing link from raw coefficient sampling to
the two explicit signed rational source sectors. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

theorem secondaryTent_source_reverse_eval₂ {K L : Type*} [CommSemiring K] [Field L]
    (f : K →+* L) (m : ℕ) (g : ℕ → K) (t : L) (ht : t≠0) :
    (secondaryTentSourceReverse m g).eval₂ f t =
      t^(m-1)*∑ v∈Finset.range m, f (g v)*t⁻¹^v := by
  classical
  rw [secondaryTentSourceReverse, eval₂_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hvm : v≤m-1 := by have :=Finset.mem_range.mp hv; omega
  simp only [eval₂_monomial, inv_pow]
  rw [pow_sub₀ _ ht hvm]
  ring

theorem secondaryTent_source_reverse_scaled_eval₂
    {K L : Type*} [CommSemiring K] [Field L]
    (f : K →+* L) (m p e : ℕ) (g : ℕ → K) (Q : K[X]) (t : L) (ht : t≠0) :
    (Q*(secondaryTentSourceReverse m g)^p).eval₂ f t *
        t⁻¹^((m-1)*p+e) =
      Q.eval₂ f t * (∑ v∈Finset.range m, f (g v)*t⁻¹^v)^p*t⁻¹^e := by
  rw [eval₂_mul, eval₂_pow, secondaryTent_source_reverse_eval₂ f m g t ht,
    mul_pow, ← pow_mul, pow_add, inv_pow, inv_pow]
  field_simp [ht]

end
end CatalanMeasure.Parametric
