module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Stieltjes
public import CatalanCore.Li2.DecayCert.Lattice.SelfEnergy
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential CatalanCore.Tools.Joukowski
noncomputable section

theorem source_real_power_integrable (s : QSegment) (y0 : ℝ) (k : ℕ)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ chebF (fun j => (s.c j:ℝ)) (s.coeff.length-1) x) :
    Integrable (fun u : ℂ => (u.re-y0)^k) s.measure := by
  change Integrable _ (segMeasure _ _ _ _)
  apply (CatalanCore.Lai.DecayEnergy.integrable_segMeasure_iff hpos (by fun_prop)).2
  apply integrable_arc_continuous
  exact (continuous_chebF_cos (fun j => (s.c j:ℝ)) (s.coeff.length-1)).mul (by fun_prop)

theorem realSegMoment_integral (s : QSegment) (y0 : ℚ) (k : ℕ) (hlen : 0 < s.coeff.length)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ chebF (fun j => (s.c j:ℝ)) (s.coeff.length-1) x) :
    (∫ u : ℂ,(u.re-(y0:ℝ))^k ∂s.measure)=(realSegMoment s y0 k:ℝ) := by
  let p := s.density*(Polynomial.C (s.mid.1-y0)+Polynomial.C s.half.1*Polynomial.X)^k
  change (∫ u : ℂ,(u.re-(y0:ℝ))^k ∂segMeasure _ _ _ _)=_
  rw [integral_segMeasure hpos (by fun_prop)]
  have he (θ : ℝ) :
      chebF (fun j => (s.c j:ℝ)) (s.coeff.length-1) (Real.cos θ)*
        ((cqReal s.mid+cqReal s.half*(Real.cos θ:ℂ)).re-(y0:ℝ))^k=
      (p.map (Rat.castHom ℝ)).eval (Real.cos θ) := by
    rw [← density_real_eval s hlen]
    dsimp only [p]
    simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_C,
      Polynomial.map_X,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_C,Polynomial.eval_X,Rat.coe_castHom,cqReal_mk,
      Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    push_cast
    ring
  simp_rw [he]
  exact arcPolyMoment_integral p

theorem source_real_power_norm (s : QSegment) (y0 : ℚ) (x : ℝ)
    (hx : x ∈ Icc (-1:ℝ) 1) :
    |(cqReal s.mid+cqReal s.half*(x:ℂ)).re-(y0:ℝ)| ≤
      ((|s.mid.1-y0|+|s.half.1|:ℚ):ℝ) := by
  simp only [cqReal_mk,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have hax : |x| ≤ 1 := abs_le.mpr hx
  have hx0 : |(s.half.1:ℝ)*x| ≤ |(s.half.1:ℝ)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hax
  have hh := abs_add_le ((s.mid.1:ℝ)-(y0:ℝ)) ((s.half.1:ℝ)*x)
  have he : (s.mid.1:ℝ)+(s.half.1:ℝ)*x-(y0:ℝ)=
      ((s.mid.1:ℝ)-(y0:ℝ))+(s.half.1:ℝ)*x := by ring
  rw [he]
  push_cast
  exact hh.trans (add_le_add (le_refl _) hx0)
#print axioms source_real_power_integrable
#print axioms realSegMoment_integral
#print axioms source_real_power_norm
end
end CatalanCore.Li2.DecayCert
