module
public import CatalanMeasure.Parametric.SecondaryTentSourceWeighted

/-! The finite physical row packet is exactly the shifted row polynomial. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem secondaryTent_source_coefficient_packet_eval {K L : Type*}
    [CommSemiring K] [Field L] (f : K →+* L) {n : ℕ} (g : ℕ)
    (R : K[X]) (hR : R.natDegree<n) (w : L) (hw : w≠0) :
    (∑ i : Fin n, f (R.coeff i.val)*w^((i.val:ℤ)-(g:ℤ))) =
      R.eval₂ f w/w^g := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (R.coeff i)*w^((i:ℤ)-(g:ℤ))),
    Polynomial.eval₂_eq_sum_range' f hR, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [zpow_natCast_sub_natCast₀ hw]
  ring

theorem secondaryTent_source_twenty_physical_packet {p N : ℕ} [Fact p.Prime]
    (R : (ZMod p)[X]) (hR : R.natDegree<20*N)
    (w : RatFunc (ZMod p)) (hw : w≠0) :
    (∑ i : Fin (20*N), algebraMap (ZMod p) (RatFunc (ZMod p)) (R.coeff i.val)*
      w^(rowOffset twenty N i.val)) =
      R.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) w/w^(2*N) := by
  simpa only [rowOffset, Parameters.g, twenty] using
    secondaryTent_source_coefficient_packet_eval
      (algebraMap (ZMod p) (RatFunc (ZMod p))) (2*N) R hR w hw

end
end CatalanMeasure.Parametric
