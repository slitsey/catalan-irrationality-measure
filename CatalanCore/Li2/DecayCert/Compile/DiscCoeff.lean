module
public import CatalanCore.Li2.DecayCert.Compile.DiscPrimitive
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem yPair_value (ζ γ q : CQ) (hs : 1 < jc (cqReal ζ)) (hq : cqReal q=jq (cqReal ζ))
    (y : ℕ → ℂ) (hy : HasTaylorSeriesAt (fun u => (jq (cqReal ζ+cqReal γ*u))⁻¹) y 0) (n : ℕ) :
    cqReal (yPair ζ γ q n).1=(if n=0 then 0 else y (n-1)) ∧
      cqReal (yPair ζ γ q n).2=y n := by
  have hr := ySeries_rec (cqReal ζ) (cqReal γ) hs y hy
  have hq0 : cqReal q ≠ 0 := by rw [hq]; exact jq_ne_zero hs
  induction n with
  | zero =>
    simp only [yPair]
    constructor
    · norm_num [cqReal]
    · rw [cqReal_inv,hq,hr.1]
  | succ n ih =>
    constructor
    · simpa only [yPair,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel_right] using ih.2
    · change cqReal (cqScale (-(1/(n+1:ℚ))) (cqDiv
        (cqAdd (cqScale ((n:ℚ)+1/2) (cqMul (cqScale 2 (cqMul ζ γ)) (yPair ζ γ q n).2))
          (cqScale (n:ℚ) (cqMul (cqMul γ γ) (yPair ζ γ q n).1))) (cqMul q q)))=y (n+1)
      simp only [cqReal_scale,cqReal_div,cqReal_add,cqReal_mul,ih.1,ih.2,hq]
      have hn : ((n+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have he := hr.2 n
      push_cast
      field_simp [hn,jq_ne_zero hs]
      push_cast at he
      linear_combination -he

theorem polynomial_hasTaylorSeriesAt_zero (p : ℂ[X]) :
    HasTaylorSeriesAt (fun u => p.eval u) (fun j => p.coeff j) 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add,Polynomial.coeff_add] using hp.add hq
  | monomial n a =>
    simpa only [Polynomial.eval_monomial,Polynomial.coeff_monomial,eq_comm] using hasTaylorSeriesAt_monomial_zero a n

theorem polynomial_affine_hasTaylorSeriesAt_zero (p : ℂ[X]) (ζ γ : ℂ) :
    HasTaylorSeriesAt (fun u => p.eval (ζ+γ*u))
      (fun j => (p.comp (C ζ+C γ*X)).coeff j) 0 := by
  have hh := polynomial_hasTaylorSeriesAt_zero (p.comp (C ζ+C γ*X))
  simpa only [Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
    Polynomial.eval_X] using hh

theorem qDensity_complex (d : QSegment) (hh : cqReal d.half ≠ 0) :
    d.density.map (Rat.castHom ℂ)=fpoly (d.toSegment hh).c (d.toSegment hh).N := by
  by_cases hz : d.coeff=[]
  · simp [QSegment.density,QSegment.c,hz,fpoly,QSegment.toSegment]
  · have hlen : d.coeff.length-1+1=d.coeff.length := by
      have := List.length_pos_iff.mpr hz
      omega
    simp only [QSegment.density,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,
      Polynomial.Chebyshev.map_T,fpoly,QSegment.toSegment,hlen,Rat.coe_castHom,Complex.ofReal_ratCast]

theorem qQuotDensity_complex (d : QSegment) (hh : cqReal d.half ≠ 0) :
    d.quotDensity.map (Rat.castHom ℂ)=rpoly (d.toSegment hh).c (d.toSegment hh).N := by
  simp only [QSegment.quotDensity,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.Chebyshev.map_U,rpoly,QSegment.toSegment,Rat.coe_castHom,Complex.ofReal_ratCast]

theorem discPrimitive_coeff_recurrence (d : SegmentData) (ζ γ : ℂ) (R : ℝ) (hR : 0 < R)
    (G : ℂ → ℂ) (hG : IsDiscSegmentPrimitive d ζ γ R G)
    (f r y b : ℕ → ℂ)
    (hf : HasTaylorSeriesAt (fun u => (fpoly d.c d.N).eval (ζ+γ*u)) f 0)
    (hr : HasTaylorSeriesAt (fun u => (rpoly d.c d.N).eval (ζ+γ*u)) r 0)
    (hy : HasTaylorSeriesAt (fun u => (jq (ζ+γ*u))⁻¹) y 0)
    (hb : HasTaylorSeriesAt G b 0) (n : ℕ) :
    (n+1:ℕ)*b (n+1)=γ*((∑ i ∈ Finset.range (n+1), f i*y (n-i))-r n) := by
  have hd : ∀ᶠ u : ℂ in nhds 0, deriv G u=
      γ*((fpoly d.c d.N).eval (ζ+γ*u)*(jq (ζ+γ*u))⁻¹-(rpoly d.c d.N).eval (ζ+γ*u)) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hR] with u hu
    rw [(discPrimitive_hasDerivAt d ζ γ R G hG u hu).deriv]
    ring
  have he := (hb.deriv.congr hd).unique (((hf.mul hy).sub hr).const_mul γ)
  exact congrFun he n

#print axioms polynomial_hasTaylorSeriesAt_zero
#print axioms polynomial_affine_hasTaylorSeriesAt_zero
#print axioms qDensity_complex
#print axioms qQuotDensity_complex
#print axioms discPrimitive_coeff_recurrence

#print axioms yPair_value
end
end CatalanCore.Li2.DecayCert
