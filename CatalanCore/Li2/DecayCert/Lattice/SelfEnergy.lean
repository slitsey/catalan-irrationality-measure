module
public import CatalanCore.Li2.DecayCert.Lattice.Defs
public import CatalanCore.Li2.DecayCert.Bent.Expressions
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential CatalanCore.Lai.DecayEnergy CatalanCore.Decay.ComplexEnergy
noncomputable section

theorem selfEnergyExpr_value (terms : ℕ) (s : QSegment) (hh : cqReal s.half ≠ 0)
    (hreal : s.half.2=0)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) x) :
    (selfEnergyExpr terms s).value=I s.measure := by
  have hI : I s.measure= -energyC s.measure := by
    change (∫ u,-(∫ y,Real.log ‖u-y‖ ∂s.measure) ∂s.measure)= -energyC s.measure
    rw [integral_neg]
    rfl
  rw [hI]
  have hE := energyC_segMeasure (M:=cqReal s.mid) hh hpos
  change energyC s.measure=_ at hE
  rw [hE]
  have hn : ‖cqReal s.half‖=|(s.half.1:ℝ)| := by
    simp only [cqReal,hreal,Rat.cast_zero,zero_mul,add_zero,← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs]
  rw [hn]
  simp only [selfEnergyExpr,seAdd_value,seScale_value,seSub_value,seRat_value,ScalarExpr.value,
    list_sum_map_range,Rat.cast_abs]
  push_cast
  congr 1 <;> ring
#print axioms selfEnergyExpr_value
end
end CatalanCore.Li2.DecayCert
