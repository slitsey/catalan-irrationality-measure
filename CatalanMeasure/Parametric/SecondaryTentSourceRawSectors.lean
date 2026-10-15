module
public import CatalanMeasure.Parametric.SecondaryTentSourceReverseEval
public import CatalanMeasure.Parametric.SecondaryTentSourceSectors

/-! The literal finite raw source, evaluated at t=2z/(1+z²), has the
two signed sectors of the human source formula. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators LaurentPolynomial
noncomputable section

def secondaryTentSourceEvaluate (p : ℕ) [Fact p.Prime] (hp2 : p≠2) :
    (ZMod p)[T;T⁻¹] →+* RatFunc (ZMod p) :=
  LaurentPolynomial.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p)))
    (Units.mk0 (palindromicRatT p) (palindromicRat_T_ne_zero hp2))

def secondaryTentSourceMacroM (p J : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  ∑ v∈Finset.range 6, algebraMap (ZMod p) (RatFunc (ZMod p))
    (palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) J)) *
      (palindromicRatT p)⁻¹^v

def secondaryTentSourceMacroZ (p J : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  ∑ v∈Finset.range 5, algebraMap (ZMod p) (RatFunc (ZMod p))
    (palindromicRatResidue p (zetaRat v J)) * (palindromicRatT p)⁻¹^v

theorem secondaryTent_source_twenty_base {p N : ℕ} [Fact p.Prime] :
    secondaryTentSourceRowBase twenty p N =
      2^(26*N)*palindromicRatW p^(26*N)*(palindromicRatW p-1)^(2*N) /
        (1+palindromicRatW p^2)^(27*N) := by
  have ht : 1-palindromicRatT p =
      (palindromicRatW p-1)^2/(1+palindromicRatW p^2) := by
    unfold palindromicRatT
    field_simp [palindromicRat_denominator_ne_zero (p:=p)]
    <;> ring
  unfold secondaryTentSourceRowBase
  rw [twenty_C]
  have hh : twenty.h N=N := by simp [Parameters.h, twenty]
  rw [hh]
  rw [ht, palindromicRatT, div_pow, div_pow, mul_pow, ← pow_mul,
    div_mul_div_comm, ← pow_add]
  rw [show N+26*N=27*N by omega]
  congr 1
  ring

theorem secondaryTent_source_reversed_laurent_eval {p : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (m e : ℕ) (g : ℕ → ZMod p) (Q : (ZMod p)[X]) :
    secondaryTentSourceEvaluate p hp2
      ((Q*(secondaryTentSourceReverse m g)^p).toLaurent *
        LaurentPolynomial.T (-(((m-1)*p+e:ℕ):ℤ))) =
      Q.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p) *
        (∑ v∈Finset.range m, algebraMap (ZMod p) (RatFunc (ZMod p)) (g v)*
          (palindromicRatT p)⁻¹^v)^p * (palindromicRatT p)⁻¹^e := by
  unfold secondaryTentSourceEvaluate
  rw [map_mul, LaurentPolynomial.eval₂_toLaurent, LaurentPolynomial.eval₂_T_neg_n]
  exact secondaryTent_source_reverse_scaled_eval₂ _ m p e g Q _
    (palindromicRat_T_ne_zero hp2)

theorem secondaryTent_source_raw_laurent_eval {P : Parameters} {p N r j : ℕ}
    [Fact p.Prime] (hp2 : p≠2) :
    secondaryTentSourceEvaluate p hp2 (secondaryTentSourceLaurentRaw P p N r j) =
      (palindromicRatT p*palindromicRatF p^(p-1)*
          (rowP P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)*
          (secondaryTentSourceMacroM p (j/p))^p -
        (3/2:RatFunc (ZMod p))*
          (rowD P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)*
          (secondaryTentSourceMacroZ p (j/p))^p) * (palindromicRatT p)⁻¹^(j%p) := by
  have hw : (oddPrimeWeight p).eval₂
      (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p) =
      palindromicRatF p^(p-1) := by
    simpa only [oddPrimeWeight, palindromicRatE, eval₂_pow, eval₂_sub,
      eval₂_one, eval₂_X] using palindromicRat_E_eq_F_pow hp2
  unfold secondaryTentSourceLaurentRaw
  have hc : secondaryTentSourceEvaluate p hp2 (LaurentPolynomial.C (3/2)) =
      (3/2:RatFunc (ZMod p)) := by
    unfold secondaryTentSourceEvaluate
    rw [LaurentPolynomial.eval₂_C, map_div₀, _root_.map_ofNat, _root_.map_ofNat]
  have hscale (L : (ZMod p)[T;T⁻¹]) :
      secondaryTentSourceEvaluate p hp2 ((3/2:ZMod p) • L) =
        (3/2:RatFunc (ZMod p))*secondaryTentSourceEvaluate p hp2 L := by
    rw [LaurentPolynomial.smul_eq_C_mul, map_mul, hc]
  rw [map_sub, hscale]
  unfold secondaryTentSourceMoment secondaryTentSourceZeta
  rw [secondaryTent_source_reversed_laurent_eval hp2 6 (j%p),
    secondaryTent_source_reversed_laurent_eval hp2 5 (j%p)]
  simp only [eval₂_mul, eval₂_X, hw, palindromicRat_int_map_eval₂]
  unfold secondaryTentSourceMacroM secondaryTentSourceMacroZ
  ring

theorem secondaryTent_source_actual_paired_rational {P : Parameters} {p N r j : ℕ}
    [Fact p.Prime] (hp2 : p≠2) (hC : 0<P.C N)
    (hd : rowDistance P N r<P.C N) :
    palindromicRatF p *
      secondaryTentSourceEvaluate p hp2 (secondaryTentSourceLaurentRaw P p N r j) =
      (palindromicRatT p)⁻¹^(j%p) * (secondaryTentSourceRowBase P p N/2) *
        (palindromicRatW p^(rowOffset P N r)*
          (palindromicRatF p*secondaryTentSourceMacroM p (j/p)+
            (3/2)*secondaryTentSourceMacroZ p (j/p))^p -
         palindromicRatW p^(-rowOffset P N r)*
          ((3/2)*secondaryTentSourceMacroZ p (j/p)-
            palindromicRatF p*secondaryTentSourceMacroM p (j/p))^p) := by
  rw [secondaryTent_source_raw_laurent_eval hp2]
  calc
    _ = (palindromicRatT p)⁻¹^(j%p) *
      (palindromicRatF p *
        (palindromicRatT p*palindromicRatF p^(p-1)*
          (rowP P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)*
          (secondaryTentSourceMacroM p (j/p))^p -
         (3/2:RatFunc (ZMod p))*
          (rowD P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)*
          (secondaryTentSourceMacroZ p (j/p))^p)) := by ring
    _ = _ := by
      rw [secondaryTent_source_paired_sectors hp2 hC hd]
      ring

end
end CatalanMeasure.Parametric
