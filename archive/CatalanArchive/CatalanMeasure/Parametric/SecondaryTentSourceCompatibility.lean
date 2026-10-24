module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceFiniteClosure
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourcePhysicalRows
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceMacroEval
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowSourceRational

/-! Literal raw source compatibility for the actual natural quotient row. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators LaurentPolynomial
noncomputable section

theorem secondaryTent_source_quotient_actual_response {p N j a g : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (hN : 0<N) (hwindow : 52*N<9*p) (hj : j<24*N)
    (hpN : 2*p≤24*N) (hag : a+g=p) (hgp : g+4*p=27*N)
    (U V : (ZMod p)[X]) (hU : U.natDegree≤4*p-1) (hV : V.natDegree≤4*p-1)
    (hd : secondaryTentRowTotalDivisor N p a ∣ secondaryTentRowNaturalNumerator p (4*p-1) U V)
    (hR : (secondaryTentRowQuotientLinear N p a
      (secondaryTentRowNaturalNumerator p (4*p-1) U V)).natDegree<20*N)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    (∑ i : Fin (20*N),
      (secondaryTentRowQuotientLinear N p a
        (secondaryTentRowNaturalNumerator p (4*p-1) U V)).coeff i.val *
      palindromicRatResidue p ((p:ℚ)^2*rawEntryRat twenty z N i.val j)) =
      (-8*2^(26*N-1):ZMod p)*
        (secondaryTentSourceNaturalSymbol p (j/p) U V).coeff (6*p-1-j%p) := by
  let f := algebraMap (ZMod p) (RatFunc (ZMod p))
  let R := secondaryTentRowQuotientLinear N p a
    (secondaryTentRowNaturalNumerator p (4*p-1) U V)
  let L := secondaryTentSourceWeightedLaurent twenty p N j (fun i : Fin (20*N) => i.val)
    (fun i => R.coeff i.val)
  let S := secondaryTentSourceNaturalSymbol p (j/p) U V
  let x := secondaryTentRowRatX p
  let s := secondaryTentRowRatS p
  let A := secondaryTentSourceMacroM p (j/p)
  let B := (3/2:RatFunc (ZMod p))*secondaryTentSourceMacroZ p (j/p)
  let u := secondaryTentRowRatU N p a (secondaryTentRowNaturalNumerator p (4*p-1) U V)
  let v := palindromicRatStar p u
  let h := secondaryTentRowRatH p N
  have h2 := palindromicRat_two_ne_zero hp2
  have hx : x≠0 := inv_ne_zero (palindromicRat_T_ne_zero hp2)
  have hs : s≠0 := mul_ne_zero (neg_ne_zero.mpr palindromicRat_F_ne_zero) hx
  have hcurve : s^2=x^2-1 := by
    dsimp [s,x]
    rw [secondaryTent_row_rat_s_coordinate hp2,secondaryTent_row_rat_x_coordinate]
    exact secondaryTent_row_rational_curve _ h2 palindromicRatW_ne_zero
  have hw : x-1≠0 := by
    intro hx1
    have hh : s^2=0 := by simpa [sub_eq_zero.mp hx1] using hcurve
    exact (pow_ne_zero 2 hs) hh
  have hjac : palindromicRatF p = -s/x := by
    change palindromicRatF p = -(-palindromicRatF p*x)/x
    simp only [neg_mul,neg_neg,mul_div_cancel_right₀ _ hx]
  have hu := secondaryTent_row_ratfunc_natural_source hp2 N a g U V hpN hag hgp hU hV hd
  have hv := secondaryTent_row_ratfunc_mirror_source hp2 N a g U V hpN hag hgp hU hV hd
  rw [secondaryTent_row_rat_star_b] at hv
  have ht := secondaryTent_source_weighted_natural_trace x s A B
    (U.eval₂ f x) (V.eval₂ f x) h u v h2 hx hs hw hcurve hu hv
  have hSeval : S.eval₂ f x =
      ((x*B-(x-1)*A)^p*U.eval₂ f x+(x*B-(x+1)*A)^p*V.eval₂ f x)/16 := by
    dsimp [S,f,x,secondaryTentRowRatX]
    rw [secondaryTent_source_natural_symbol_eval,
      secondaryTent_source_moment_macro_eval,secondaryTent_source_zeta_macro_eval]
  rw [← hSeval] at ht
  have hphysical := secondaryTent_source_twenty_physical_packet R hR
    (palindromicRatW p) palindromicRatW_ne_zero
  change (∑ i : Fin (20*N), f (R.coeff i.val)*
    palindromicRatW p^(rowOffset twenty N i.val))=u at hphysical
  have hmirror := congrArg (palindromicRatStar p) hphysical
  simp only [f,map_sum,map_mul,map_zpow₀,palindromicRatStar_scalar,palindromicRatStar_W,
    inv_zpow,← zpow_neg] at hmirror
  have hC : 0<twenty.C N := by rw [twenty_C]; omega
  have hdist (i : Fin (20*N)) : rowDistance twenty N i.val<twenty.C N :=
    rowDistance_lt_C twenty_admissible hN i.isLt
  have hpair := secondaryTent_source_weighted_paired (P:=twenty) (N:=N) (j:=j) hp2
    hC (fun i : Fin (20*N) => i.val) (fun i => R.coeff i.val) hdist
  rw [hphysical,hmirror] at hpair
  have hbase : secondaryTentSourceRowBase twenty p N=2^(26*N)*h := by
    dsimp [h,secondaryTentRowRatH]
    field_simp [h2]
  have hpair' : palindromicRatF p*secondaryTentSourceEvaluate p hp2 L =
      x^(j%p)*(2^(26*N)*h/2)*(u*(B-s*A/x)^p-v*(B+s*A/x)^p) := by
    rw [hbase] at hpair
    convert hpair using 1 <;> dsimp only [L,x,secondaryTentRowRatX,B,A,v] <;>
      rw [hjac] <;> dsimp only [x,secondaryTentRowRatX] <;> ring
  have heval := secondaryTent_source_signed_trace_scale hN (Fact.out : p.Prime).pos
    (Nat.mod_lt j (Fact.out : p.Prime).pos) x s (palindromicRatF p)
    (secondaryTentSourceEvaluate p hp2 L) (S.eval₂ f x) h u v A B
    h2 hx palindromicRat_F_ne_zero hjac hpair' ht
  have heval' : secondaryTentSourceEvaluate p hp2 L =
      f (-8*2^(26*N-1):ZMod p)*S.eval₂ f (palindromicRatT p)⁻¹*
        palindromicRatT p^(6*p-1-j%p) := by
    simpa only [f,map_mul,map_neg,map_pow,_root_.map_ofNat,x,secondaryTentRowRatX,
      div_eq_mul_inv,inv_pow,inv_inv] using heval
  rw [secondaryTent_source_weighted_actual hN hwindow hj (fun i : Fin (20*N) => i.val)
    (fun i => R.coeff i.val) z hzp]
  exact secondaryTent_source_reflected_unique hp2 L S _ _ heval'

end
end CatalanMeasure.Parametric
