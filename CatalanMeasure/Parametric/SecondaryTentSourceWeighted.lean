module
public import CatalanMeasure.Parametric.SecondaryTentSourceRawSectors

/-! Linear aggregation of the literal finite source over actual rows. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators LaurentPolynomial
noncomputable section

def secondaryTentSourceWeightedLaurent {ι : Type*} [Fintype ι]
    (P : Parameters) (p N j : ℕ) [Fact p.Prime]
    (rows : ι → ℕ) (c : ι → ZMod p) : (ZMod p)[T;T⁻¹] :=
  ∑ i, c i • secondaryTentSourceLaurentRaw P p N (rows i) j

theorem secondaryTent_source_weighted_actual {p N j : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] (hN : 0<N) (hwindow : 52*N<9*p) (hj : j<24*N)
    (rows : ι → ℕ) (c : ι → ZMod p)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    (∑ i, c i*palindromicRatResidue p ((p:ℚ)^2*rawEntryRat twenty z N (rows i) j)) =
      (secondaryTentSourceWeightedLaurent twenty p N j rows c).coeff 0 := by
  classical
  unfold secondaryTentSourceWeightedLaurent
  let ev : (ZMod p)[T;T⁻¹] →+ ZMod p :=
    { toFun := fun L => L.coeff 0
      map_zero' := rfl
      map_add' := fun F G => by
        simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] }
  change _ = ev (∑ i, c i • secondaryTentSourceLaurentRaw twenty p N (rows i) j)
  rw [map_sum]
  change _ = ∑ i, (c i • secondaryTentSourceLaurentRaw twenty p N (rows i) j).coeff 0
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hh := secondaryTent_source_twenty_laurent_substitution
    (r:=rows i) hN hwindow hj z hzp
  rw [secondaryTent_source_substitution_finite] at hh
  rw [hh]

theorem secondaryTent_source_weighted_paired {P : Parameters} {p N j : ℕ}
    [Fact p.Prime] {ι : Type*} [Fintype ι] (hp2 : p≠2) (hC : 0<P.C N)
    (rows : ι → ℕ) (c : ι → ZMod p)
    (hd : ∀ i, rowDistance P N (rows i)<P.C N) :
    palindromicRatF p * secondaryTentSourceEvaluate p hp2
        (secondaryTentSourceWeightedLaurent P p N j rows c) =
      (palindromicRatT p)⁻¹^(j%p)*(secondaryTentSourceRowBase P p N/2) *
        ((∑ i, algebraMap (ZMod p) (RatFunc (ZMod p)) (c i)*
            palindromicRatW p^(rowOffset P N (rows i))) *
          (palindromicRatF p*secondaryTentSourceMacroM p (j/p)+
            (3/2)*secondaryTentSourceMacroZ p (j/p))^p -
         (∑ i, algebraMap (ZMod p) (RatFunc (ZMod p)) (c i)*
            palindromicRatW p^(-rowOffset P N (rows i))) *
          ((3/2)*secondaryTentSourceMacroZ p (j/p)-
            palindromicRatF p*secondaryTentSourceMacroM p (j/p))^p) := by
  classical
  have hscale (a : ZMod p) (L : (ZMod p)[T;T⁻¹]) :
      secondaryTentSourceEvaluate p hp2 (a • L) =
      algebraMap (ZMod p) (RatFunc (ZMod p)) a*secondaryTentSourceEvaluate p hp2 L := by
    rw [LaurentPolynomial.smul_eq_C_mul, map_mul]
    simp only [secondaryTentSourceEvaluate, LaurentPolynomial.eval₂_C]
  unfold secondaryTentSourceWeightedLaurent
  rw [map_sum, Finset.mul_sum]
  simp only [hscale]
  calc
    _ = ∑ i, algebraMap (ZMod p) (RatFunc (ZMod p)) (c i)*
      (palindromicRatF p*secondaryTentSourceEvaluate p hp2
        (secondaryTentSourceLaurentRaw P p N (rows i) j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, algebraMap (ZMod p) (RatFunc (ZMod p)) (c i)*
      ((palindromicRatT p)⁻¹^(j%p)*(secondaryTentSourceRowBase P p N/2) *
        (palindromicRatW p^(rowOffset P N (rows i))*
          (palindromicRatF p*secondaryTentSourceMacroM p (j/p)+
            (3/2)*secondaryTentSourceMacroZ p (j/p))^p -
         palindromicRatW p^(-rowOffset P N (rows i))*
          ((3/2)*secondaryTentSourceMacroZ p (j/p)-
            palindromicRatF p*secondaryTentSourceMacroM p (j/p))^p)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [secondaryTent_source_actual_paired_rational hp2 hC (hd i)]
    _ = _ := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

end
end CatalanMeasure.Parametric
