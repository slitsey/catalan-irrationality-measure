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

theorem latticeShapeCheck_parts (d : LatticeInput) (hc : latticeShapeCheck d=true) :
    0 < d.Y ∧ d.first.mid=(d.Y/2,0) ∧ d.first.half=(d.Y/2,0) ∧
    d.second.mid.2=0 ∧ d.second.half.2=0 ∧
    -4 ≤ d.second.mid.1-d.second.half.1 ∧ d.second.mid.1-d.second.half.1 ≤ -1 ∧
    -4 ≤ d.second.mid.1+d.second.half.1 ∧ d.second.mid.1+d.second.half.1 ≤ -1 :=
  of_decide_eq_true hc

theorem lattice_sources (d : LatticeInput) : d.data.dual.σ=d.first.measure+d.second.measure := by
  rw [d.data.measure_eq,d.source_eq]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]

theorem datum_source_data (d : SegmentDatum) (dw : DensityWitness) (hd : datumCheck d dw=true)
    (s : QSegment) (hs : s ∈ d.segments) :
    cqReal s.half ≠ 0 ∧ 0 < s.coeff.length ∧
      ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) x := by
  rcases (sourceDataCheck_parts d.segments d.radius dw hd).2 s hs with ⟨t,ht,hbern⟩
  exact ⟨half_ne_of_cqSq_ne s.half ht.1,ht.2.1,(datumCheck_positive d dw hd).1 s hs⟩

theorem lattice_first_mem (d : LatticeInput) : d.first ∈ d.data.segments := by rw [d.source_eq]; simp

theorem lattice_second_mem (d : LatticeInput) : d.second ∈ d.data.segments := by rw [d.source_eq]; simp

theorem lattice_first_support (d : LatticeInput) (hc : latticeShapeCheck d=true) :
    d.first.measure {s | s.im ≠ 0 ∨ s.re < 0 ∨ (d.Y:ℝ) < s.re}=0 := by
  have h := latticeShapeCheck_parts d hc
  have hsupport := LatticeGate.segment_real_support d.first 0 d.Y
  simp only [Rat.cast_zero] at hsupport
  apply hsupport
  · rw [h.2.1]
  · rw [h.2.2.1]
  · rw [h.2.1,h.2.2.1]
    dsimp only [Prod.fst]
    constructor <;> linarith [h.1]
  · rw [h.2.1,h.2.2.1]
    dsimp only [Prod.fst]
    constructor <;> linarith [h.1]

theorem lattice_second_support (d : LatticeInput) (hc : latticeShapeCheck d=true) :
    d.second.measure {s | s.im ≠ 0 ∨ s.re < (-4:ℝ) ∨ (-1:ℝ) < s.re}=0 := by
  have h := latticeShapeCheck_parts d hc
  have hsupport := LatticeGate.segment_real_support d.second (-4) (-1) h.2.2.2.1 h.2.2.2.2.1
  norm_num only [Rat.cast_neg,Rat.cast_ofNat,Rat.cast_one] at hsupport
  apply hsupport
  · exact ⟨h.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1⟩
  · exact ⟨h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2⟩

theorem datum_subsource_U_integrable (d : DualDatum) (μ ν : Measure ℂ)
    (hμ : μ ≤ d.σ) (hν : ν ≤ d.σ) : Integrable (U μ) ν := by
  haveI := d.finite
  haveI : IsFiniteMeasure μ := isFiniteMeasure_of_le d.σ hμ
  haveI : IsFiniteMeasure ν := isFiniteMeasure_of_le d.σ hν
  have hh := d.selfIntegrable.mono_measure (Measure.prod_mono hν hμ)
  change Integrable (fun u => -(∫ y,Real.log ‖u-y‖ ∂μ)) ν
  exact hh.integral_prod_left.neg
#print axioms lattice_sources
#print axioms datum_source_data
#print axioms lattice_first_support
#print axioms lattice_second_support
#print axioms datum_subsource_U_integrable
end
end CatalanCore.Li2.DecayCert
