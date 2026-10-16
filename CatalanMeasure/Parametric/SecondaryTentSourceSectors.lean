module
public import CatalanMeasure.Parametric.SecondaryTentSourceDigit
public import CatalanMeasure.Parametric.SparseRowEvaluation

/-! Both signed Chebyshev sectors of the actual row source. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

def secondaryTentSourceRowBase (P : Parameters) (p N : ℕ) [Fact p.Prime] :
    RatFunc (ZMod p) :=
  (1-palindromicRatT p)^(P.h N) * palindromicRatT p^(P.C N)

/-- Negating the signed Chebyshev index gives the mirror sector with
exactly the opposite U sign, including negative physical row offsets. -/
theorem secondaryTent_source_chebyshev_mirror {p : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (m : ℤ) :
    palindromicRatT p *
        (Chebyshev.T ℤ m).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p)⁻¹ +
      palindromicRatF p *
        (Chebyshev.U ℤ (m-1)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p)⁻¹ =
      palindromicRatT p * palindromicRatW p^(-m) := by
  simpa only [Chebyshev.T_neg, Chebyshev.U_neg_sub_one, eval₂_neg,
    mul_neg, sub_neg_eq_add] using palindromicRat_chebyshev_signed hp2 (-m)

theorem secondaryTent_source_row_mirror {P : Parameters} {p N r : ℕ}
    [Fact p.Prime] (hp2 : p≠2) (hC : 0<P.C N)
    (hd : rowDistance P N r<P.C N) :
    palindromicRatT p *
        (rowP P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p) +
      palindromicRatF p *
        (rowD P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p) =
      secondaryTentSourceRowBase P p N * palindromicRatW p^(-rowOffset P N r) := by
  rw [rowP_eval₂_signed _ hd (palindromicRat_T_ne_zero hp2),
    rowD_eval₂_signed _ hd (palindromicRat_T_ne_zero hp2)]
  have hpow : palindromicRatT p^(P.C N-1)*palindromicRatT p =
      palindromicRatT p^(P.C N) := by
    rw [← pow_succ, Nat.sub_add_cancel hC]
  calc
    _ = (1-palindromicRatT p)^(P.h N)*palindromicRatT p^(P.C N-1)*
      (palindromicRatT p *
        (Chebyshev.T ℤ (rowOffset P N r)).eval₂
          (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)⁻¹ +
       palindromicRatF p *
        (Chebyshev.U ℤ (rowOffset P N r-1)).eval₂
          (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)⁻¹) := by ring
    _ = (1-palindromicRatT p)^(P.h N)*palindromicRatT p^(P.C N-1)*
      (palindromicRatT p*palindromicRatW p^(-rowOffset P N r)) := by
      rw [secondaryTent_source_chebyshev_mirror hp2]
    _ = _ := by unfold secondaryTentSourceRowBase; rw [← hpow]; ring

/-- Exact symmetric and antisymmetric sectors of the actual row polynomials. -/
theorem secondaryTent_source_row_sectors {P : Parameters} {p N r : ℕ}
    [Fact p.Prime] (hp2 : p≠2) (hC : 0<P.C N)
    (hd : rowDistance P N r<P.C N) :
    (palindromicRatT p *
      (rowP P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p) =
        (secondaryTentSourceRowBase P p N/2) *
          (palindromicRatW p^(rowOffset P N r)+palindromicRatW p^(-rowOffset P N r))) ∧
    (palindromicRatF p *
      (rowD P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p) =
        (secondaryTentSourceRowBase P p N/2) *
          (palindromicRatW p^(-rowOffset P N r)-palindromicRatW p^(rowOffset P N r))) := by
  have hm := rat_row_identity (P:=P) hp2 hC hd
  change _ = secondaryTentSourceRowBase P p N*palindromicRatW p^(rowOffset P N r) at hm
  have hp := secondaryTent_source_row_mirror hp2 hC hd
  have htwo := palindromicRat_two_ne_zero hp2
  constructor
  · field_simp
    linear_combination hm+hp
  · field_simp
    linear_combination hp-hm

/-- The actual transformed source splits into its two Laurent sectors,
with the same scalar and opposite mirror sign. Here M,Z are the literal
finite forward source sums; the theorem applies to them without any
rank, residue, or Cartier hypothesis. -/
theorem secondaryTent_source_paired_sectors {P : Parameters} {p N r : ℕ}
    [hp : Fact p.Prime] (hp2 : p≠2) (hC : 0<P.C N)
    (hd : rowDistance P N r<P.C N) (M Z : RatFunc (ZMod p)) :
    palindromicRatF p *
      (palindromicRatT p*palindromicRatF p^(p-1)*
        (rowP P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)*M^p -
       (3/2:RatFunc (ZMod p))*
        (rowD P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)*Z^p) =
      (secondaryTentSourceRowBase P p N/2) *
        (palindromicRatW p^(rowOffset P N r)*(palindromicRatF p*M+(3/2)*Z)^p -
         palindromicRatW p^(-rowOffset P N r)*((3/2)*Z-palindromicRatF p*M)^p) := by
  have hsect := secondaryTent_source_row_sectors hp2 hC hd
  have hthree : (3:RatFunc (ZMod p))^p=3 := by
    have hh := add_pow_char (2:RatFunc (ZMod p)) 1 p
    norm_num only [one_pow, palindromicRat_two_pow] at hh
    convert hh using 1 <;> norm_num
  have hc : (3/2:RatFunc (ZMod p))^p=3/2 := by
    rw [div_pow, hthree, palindromicRat_two_pow]
  have hpow : palindromicRatF p*palindromicRatF p^(p-1)=palindromicRatF p^p := by
    rw [← pow_succ', Nat.sub_add_cancel hp.out.pos]
  have hsource :
      palindromicRatF p *
        (palindromicRatT p*palindromicRatF p^(p-1)*
          (rowP P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)*M^p -
         (3/2:RatFunc (ZMod p))*
          (rowD P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)*Z^p) =
      (palindromicRatT p*
        (rowP P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p))*
          palindromicRatF p^p*M^p -
      (3/2:RatFunc (ZMod p))*(palindromicRatF p*
        (rowD P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p))*Z^p := by
    linear_combination (norm:=ring_nf)
      (palindromicRatT p*
        (rowP P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)*M^p)*hpow
  rw [hsource, hsect.1, hsect.2, add_pow_char, sub_pow_char, mul_pow, mul_pow, hc]
  ring

end
end CatalanMeasure.Parametric
