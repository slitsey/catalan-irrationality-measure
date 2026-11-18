module
public import CatalanCore.Li2.DecayCert.Density.Source
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
noncomputable section

noncomputable def datumOfSourceChecks (ss : List QSegment) (R : ℚ) (w : DensityWitness)
    (hc : sourceDataCheck ss R w=true) : SegmentDatum :=
  ⟨ss,Classical.choose (checkedDatum_exists ss R w hc),Classical.choose_spec (checkedDatum_exists ss R w hc),R⟩

theorem datumOfSourceChecks_segments (ss : List QSegment) (R : ℚ) (w : DensityWitness)
    (hc : sourceDataCheck ss R w=true) : (datumOfSourceChecks ss R w hc).segments=ss := rfl

theorem datumOfSourceChecks_radius (ss : List QSegment) (R : ℚ) (w : DensityWitness)
    (hc : sourceDataCheck ss R w=true) : (datumOfSourceChecks ss R w hc).radius=R := rfl

theorem datumCheck_positive (d : SegmentDatum) (w : DensityWitness) (h : datumCheck d w=true) :
    (∀ s ∈ d.segments,∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (s.c k:ℝ)) (s.coeff.length-1) x) ∧
      (∀ᵐ u ∂d.dual.σ,‖u‖ ≤ (d.radius:ℝ)) := by
  have hc : sourceDataCheck d.segments d.radius w=true := h
  refine ⟨sourceDataCheck_positive d.segments d.radius w hc,?_⟩
  rw [d.measure_eq]
  exact sourceDataCheck_supported d.segments d.radius w hc

theorem segment_endpoint_atomless (s : QSegment)
    (hp : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (s.c k:ℝ)) (s.coeff.length-1) x)
    (hh : cqSq s.half ≠ 0) (z : ℂ) : s.measure {z}=0 := by
  rcases segment_ballMaj_exists s (half_ne_of_cqSq_ne s.half hh) with ⟨b,A,hb⟩
  exact hb.singleton_zero z

theorem atomCapCheck_bound (s : QSegment) (w : AtomCapWitness) (hc : atomCapCheck s w=true) :
    ∀ x ∈ Icc (-1:ℝ) 1,Real.sqrt (1-x^2)*(w.g.map (Rat.castHom ℝ)).eval x/
      (Real.pi*|(s.half.1:ℝ)|) ≤ 1 := by
  unfold atomCapCheck at hc
  simp only [Bool.and_eq_true,decide_eq_true_eq,and_assoc] at hc
  rcases hc with ⟨hmid,hhalf,hne,hc0,hfactor,hgcheck,hbcheck,hclcheck⟩
  have hg := bernCheck_sound w.g (-1) 1 w.positive hgcheck
  have hb := bernCheck_sound (Polynomial.C (w.c^2)-(1-Polynomial.X^2)*w.g^2) (-1) 1 w.cap hbcheck
  have hcl := scalarLowerCheck_sound w.c (seScale |s.half.1| .pi) hclcheck
  have hcl' : (w.c:ℝ) ≤ |(s.half.1:ℝ)| *Real.pi := by
    simpa only [seScale,seMul,seRat,ScalarExpr.value,Rat.cast_abs] using hcl
  have hr : 0 < |(s.half.1:ℝ)| := abs_pos.mpr (by exact_mod_cast hne)
  have hcc : 0 ≤ (w.c:ℝ) := by exact_mod_cast hc0
  apply atom_density_cap (w.g.map (Rat.castHom ℝ)) _ _ hr ⟨hcc,by linarith [hcl']⟩
  · intro x hx
    exact hg x (by simpa only [Rat.cast_neg,Rat.cast_one] using hx)
  · intro x hx
    have hh := hb x (by simpa only [Rat.cast_neg,Rat.cast_one] using hx)
    simp only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,
      Polynomial.map_one,Polynomial.map_X,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_C,Polynomial.eval_one,Polynomial.eval_X,Rat.coe_castHom,Rat.cast_pow] at hh
    linarith

#print axioms datumOfSourceChecks_segments
#print axioms datumOfSourceChecks_radius
#print axioms datumCheck_positive
#print axioms segment_endpoint_atomless
#print axioms atomCapCheck_bound
end
end CatalanCore.Li2.DecayCert
