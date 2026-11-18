module
public import CatalanCore.Li2.DecayCert.Lattice.Cross
public import CatalanCore.Li2.DecayCert.Lattice.Shape
public import CatalanCore.Li2.DecayCert.Lattice.Seed
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential
noncomputable section

theorem latticeEnergyExpr_upper (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (hshape : latticeShapeCheck d=true)
    (w : LatticeEnergyWitness) (e : SE) (he : latticeEnergyExpr d w=some e) :
    I d.data.dual.σ ≤ e.value := by
  let ξ : ℚ := (w.phi+w.phi⁻¹)/2
  let y0 : ℚ := d.first.mid.1-d.first.half.1*ξ
  let H : ℚ := |d.second.mid.1-y0|+|d.second.half.1|
  let v : ℚ := H/(-y0)
  let cross : ℚ := ((List.range w.order).map (fun k : ℕ =>
    realSegMoment d.second y0 (k+1)*stieltjesQ d.first w.phi (k+1)/(k+1:ℚ))).sum
  let err : ℚ := 2*d.second.c 0*d.first.c 0*v^(w.order+1)/((w.order+1:ℚ)*(1-v))
  change (if 1 < w.phi ∧ y0 < 0 ∧ 0 ≤ v ∧ v < 1 then
    some (seSum [selfEnergyExpr w.terms d.first,selfEnergyExpr w.terms d.second,
      seScale (2*d.second.c 0) (latticeLeftSeed w.terms d.first w.phi),seRat (2*cross+err)])
    else none)=some e at he
  split at he
  · rename_i hg
    have heq := Option.some.inj he
    have hs := latticeShapeCheck_parts d hshape
    have hp1 := datum_source_data d.data dw hd d.first (lattice_first_mem d)
    have hp2 := datum_source_data d.data dw hd d.second (lattice_second_mem d)
    haveI := positive_source_finite d.first hp1.2.2
    haveI := positive_source_finite d.second hp2.2.2
    have hhpos : 0 < d.first.half.1 := by rw [hs.2.2.1]; dsimp only [Prod.fst]; linarith [hs.1]
    have hm1 : d.first.mid.2=0 := by rw [hs.2.1]
    have hh1 : d.first.half.2=0 := by rw [hs.2.2.1]
    have hm2 : d.second.mid.2=0 := hs.2.2.2.1
    have hh2 : d.second.half.2=0 := hs.2.2.2.2.1
    have hμ1 : d.first.measure ≤ d.data.dual.σ := by
      rw [d.data.measure_eq]
      exact source_measure_le_sum _ _ (lattice_first_mem d)
    have hμ2 : d.second.measure ≤ d.data.dual.σ := by
      rw [d.data.measure_eq]
      exact source_measure_le_sum _ _ (lattice_second_mem d)
    have hInt := datum_subsource_U_integrable d.data.dual d.first.measure d.second.measure hμ1 hμ2
    have hHq : 0 ≤ H := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsepQ : H < -y0 := by
      have hv : H/(-y0) < 1 := hg.2.2.2
      exact (div_lt_one (neg_pos.mpr hg.2.1)).mp hv
    have hyR : (y0:ℝ) < 0 := by exact_mod_cast hg.2.1
    have hHR : (0:ℝ) ≤ (H:ℝ) := by exact_mod_cast hHq
    have hYR : (0:ℝ) ≤ (d.Y:ℝ) := by exact_mod_cast hs.1.le
    have hsepR : (H:ℝ) < -(y0:ℝ) := by exact_mod_cast hsepQ
    have hprojection := source_real_projection d.second y0 hm2 hh2
    have hb := cross_stieltjes_integral_bound d.first.measure d.second y0 (H:ℝ) (d.Y:ℝ) w.order
      hp2.2.1 hp2.2.2 hyR hHR hYR hsepR (lattice_first_support d hshape) hprojection hInt
    rw [positive_source_mass d.first hp1.2.2] at hb
    have hinv (k : ℕ) : inverseMoment d.first.measure (y0:ℝ) k=(stieltjesQ d.first w.phi k:ℝ) := by
      exact inverseMoment_stieltjesQ d.first w.phi hg.1 hhpos hp1.2.2 k
    simp_rw [hinv] at hb
    have hseed : (latticeLeftSeed w.terms d.first w.phi).value=U d.first.measure ((y0:ℝ):ℂ) :=
      latticeLeftSeed_value w.terms d.first w.phi hg.1 hhpos hm1 hh1 hp1.2.2
    rw [← hseed] at hb
    have hcross : (cross:ℝ)=∑ k ∈ Finset.range w.order,
        (realSegMoment d.second y0 (k+1):ℝ)*(stieltjesQ d.first w.phi (k+1):ℝ)/(k+1:ℕ) := by
      dsimp only [cross]
      rw [list_sum_map_range]
      push_cast
      rfl
    rw [← hcross] at hb
    have herr : (err:ℝ)=2*(d.second.c 0:ℝ)*mpErr (d.first.c 0:ℝ) ((H:ℝ)/(-(y0:ℝ))) w.order := by
      dsimp only [err,v,mpErr]
      push_cast
      ring
    rw [← heq,seSum_value]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,seScale_value,seRat_value,add_zero]
    rw [selfEnergyExpr_value w.terms d.first hp1.1 hh1 hp1.2.2,
      selfEnergyExpr_value w.terms d.second hp2.1 hh2 hp2.2.2,
      datum_energy_two d.data.dual d.first.measure d.second.measure (lattice_sources d)]
    push_cast
    rw [herr]
    linarith
  · simp at he
#print axioms latticeEnergyExpr_upper
end
end CatalanCore.Li2.DecayCert
