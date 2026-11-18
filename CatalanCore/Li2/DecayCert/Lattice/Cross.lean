module
public import CatalanCore.Li2.DecayCert.Lattice.Ordinary
public import CatalanCore.Li2.DecayCert.Lattice.EnergyBilinear
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential
noncomputable section

theorem source_real_projection (s : QSegment) (y0 : ℚ) (hm : s.mid.2=0) (hh : s.half.2=0) :
    ∀ᵐ u : ℂ ∂s.measure,u.im=0 ∧ |u.re-(y0:ℝ)| ≤ ((|s.mid.1-y0|+|s.half.1|:ℚ):ℝ) := by
  rw [← sourceParameter_map s]
  apply (ae_map_iff (by fun_prop) (by measurability)).2
  filter_upwards [ae_iff.mpr (sourceParameter_supported s)] with x hx
  refine ⟨?_,source_real_power_norm s y0 x hx⟩
  simp [cqReal,hm,hh]

theorem cross_stieltjes_integral_bound (σ : Measure ℂ) [IsFiniteMeasure σ]
    (s : QSegment) (y0 : ℚ) (H Y : ℝ) (K : ℕ)
    (hlen : 0 < s.coeff.length)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ chebF (fun j => (s.c j:ℝ)) (s.coeff.length-1) x)
    (hy : (y0:ℝ) < 0) (hH : 0 ≤ H) (hY : 0 ≤ Y) (hsep : H < -(y0:ℝ))
    (hs : σ {u | u.im ≠ 0 ∨ u.re < 0 ∨ Y < u.re}=0)
    (hsreal : ∀ᵐ u : ℂ ∂s.measure,u.im=0 ∧ |u.re-(y0:ℝ)| ≤ H)
    (hInt : Integrable (U σ) s.measure) :
    (∫ u,U σ u ∂s.measure) ≤ (s.c 0:ℝ)*U σ ((y0:ℝ):ℂ)+
      (∑ k ∈ Finset.range K,(realSegMoment s y0 (k+1):ℝ)*inverseMoment σ (y0:ℝ) (k+1)/(k+1:ℕ))+
      (s.c 0:ℝ)*mpErr (σ.real univ) (H/(-(y0:ℝ))) K := by
  haveI := positive_source_finite s hpos
  let err := mpErr (σ.real univ) (H/(-(y0:ℝ))) K
  let term : ℕ → ℂ → ℝ := fun k u => inverseMoment σ (y0:ℝ) (k+1)*(u.re-(y0:ℝ))^(k+1)/(k+1:ℕ)
  let poly : ℂ → ℝ := fun u => U σ ((y0:ℝ):ℂ)+∑ k ∈ Finset.range K,term k u
  have hterm (k : ℕ) : Integrable (term k) s.measure :=
    ((source_real_power_integrable s (y0:ℝ) (k+1) hpos).const_mul _).div_const _
  have hsum : Integrable (fun u => ∑ k ∈ Finset.range K,term k u) s.measure :=
    integrable_finset_sum _ (fun k hk => hterm k)
  have hpoly : Integrable poly s.measure := (integrable_const _).add hsum
  have hmodel := logPot_stieltjes_model σ (y0:ℝ) H Y hy hH hY hsep hs K
  have hb : ∀ᵐ u : ℂ ∂s.measure,U σ u ≤ poly u+err := by
    filter_upwards [hsreal] with u hu
    have hh := hmodel.2.2 (u.re-(y0:ℝ)) hu.2
    rw [evalModel_stieltjesCoeffs,Finset.sum_range_succ'] at hh
    simp only [Nat.cast_zero,div_zero,add_zero] at hh
    have he : (y0:ℝ)+(u.re-(y0:ℝ))=u.re := by ring
    have hure : (u.re:ℂ)=u := by apply Complex.ext <;> simp [hu.1]
    rw [he,hure] at hh
    have hle := (abs_le.mp hh).2
    dsimp only [poly,term,err]
    linarith
  have hepoly : (∫ u,poly u ∂s.measure)=(s.c 0:ℝ)*U σ ((y0:ℝ):ℂ)+
      ∑ k ∈ Finset.range K,(realSegMoment s y0 (k+1):ℝ)*inverseMoment σ (y0:ℝ) (k+1)/(k+1:ℕ) := by
    rw [show poly=(fun u => U σ ((y0:ℝ):ℂ)+∑ k ∈ Finset.range K,term k u) from rfl,
      integral_add (integrable_const _) hsum,integral_const,smul_eq_mul,positive_source_mass s hpos,
      integral_finsetSum _ (fun k hk => hterm k)]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [term]
    rw [integral_div,integral_const_mul,realSegMoment_integral s y0 (k+1) hlen hpos]
    ring
  have hi := integral_mono_ae hInt (hpoly.add (integrable_const err)) hb
  simp only [Pi.add_apply] at hi
  rw [integral_add hpoly (integrable_const err),integral_const,smul_eq_mul,positive_source_mass s hpos,hepoly] at hi
  exact hi
#print axioms source_real_projection
#print axioms cross_stieltjes_integral_bound
end
end CatalanCore.Li2.DecayCert
