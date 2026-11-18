module
public import CatalanCore.Li2.DecayCert.Covers.Clipped
public import CatalanCore.Li2.DecayCert.Covers.Recenter
public import CatalanCore.Li2.DecayCert.Covers.Geometry
public import CatalanCore.Li2.DecayCert.Covers.EnergyLower
public import CatalanCore.Li2.DecayCert.Covers.LinePartition
public import CatalanCore.Li2.DecayCert.Covers.Symmetry
public import CatalanCore.Li2.DecayCert.Covers.EnergyIntegral
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential
noncomputable section
theorem energy_up_bent_labelled (z : ℚ) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true) (hp : placementCheck b=true)
    (es : List EnergyPiece) (hc : energyCoverCheck b es=true) (lower : ℕ → ℚ)
    (hlo : ∀ i : Fin es.length, ∀ j : Fin (baseSegments b).length,
      (es[i]).segment=j.val →
      ∀ᵐ x : ℝ ∂((baseSegments b)[j]).parameterMeasure.restrict
        (Icc ((es[i]).left.x:ℝ) ((es[i]).right.x:ℝ)),
        (lower i.val:ℝ) ≤ W (z:ℝ) b.data.dual.σ
          (cqReal ((baseSegments b)[j]).mid+cqReal ((baseSegments b)[j]).half*(x:ℂ)))
    (hV : Integrable (V (z:ℝ)) b.data.dual.σ)
    (hU : Integrable (U b.data.dual.σ) b.data.dual.σ) :
  I b.data.dual.σ ≤ ((∫ s, V (z:ℝ) s ∂b.data.dual.σ) -
    ∑ j : Fin (baseSegments b).length,
      (if j.val < b.upper.length then 2 else 1) *
        ∑ i : Fin es.length, if (es[i]).segment=j.val then
          (lower i.val:ℝ) * ((baseSegments b)[j]).parameterMeasure.real
            (Icc ((es[i]).left.x:ℝ) ((es[i]).right.x:ℝ)) else 0)/2 := by
  classical
  have hW : Integrable (W (z:ℝ) b.data.dual.σ) b.data.dual.σ := hV.sub (hU.const_mul 2)
  let low (j : Fin (baseSegments b).length) : ℝ :=
    ∑ i : Fin es.length,if (es[i]).segment=j.val then
      (lower i.val:ℝ)*((baseSegments b)[j]).parameterMeasure.real
        (Icc ((es[i]).left.x:ℝ) ((es[i]).right.x:ℝ)) else 0
  have hj (j : Fin (baseSegments b).length) : low j ≤
      ∫ u,W (z:ℝ) b.data.dual.σ u ∂((baseSegments b)[j]).measure := by
    let s := (baseSegments b)[j]
    let cells (i : Fin es.length) : Set ℝ := if (es[i]).segment=j.val then
      Icc ((es[i]).left.x:ℝ) ((es[i]).right.x:ℝ) else ∅
    haveI := source_parameter_finite s
    have hs : s.measure ≤ b.data.dual.σ := by
      rw [b.data.measure_eq]
      exact source_measure_le_sum b.data.segments s
        (baseSegments_mem_data b s (List.getElem_mem _))
    have hf := hW.mono_measure hs
    have hp0 := energyCoverCheck_partition b es hc j
    have hmeas (i : Fin es.length) : MeasurableSet (cells i) := by
      dsimp only [cells]
      split_ifs
      · exact measurableSet_Icc
      · exact MeasurableSet.empty
    have hn (i k : Fin es.length) (hik : i ≠ k) : s.parameterMeasure (cells i ∩ cells k)=0 := by
      dsimp only [cells]
      split_ifs with hi hk hk
      · exact hp0.2 i k hik hi hk
      all_goals simp
    have hl (i : Fin es.length) : ∀ᵐ x : ℝ ∂s.parameterMeasure.restrict (cells i),
        (lower i.val:ℝ) ≤ W (z:ℝ) b.data.dual.σ (cqReal s.mid+cqReal s.half*(x:ℂ)) := by
      dsimp only [cells]
      split_ifs with hi
      · exact hlo i j hi
      · simp
    have hb := parameter_partition_lower s.parameterMeasure _ (source_parameter_integrable s _ hf)
      cells (fun i => (lower i.val:ℝ)) hmeas hp0.1 hn hl
    rw [source_parameter_integral s _ hf] at hb
    have he : (∑ i : Fin es.length,s.parameterMeasure.real (cells i)*(lower i.val:ℝ))=low j := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [cells,low,s]
      split_ifs <;> simp [mul_comm]
    rwa [he] at hb
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ =>
    mul_le_mul_of_nonneg_left (hj j)
      (show (0:ℝ) ≤ (if j.val < b.upper.length then 2 else 1) by split_ifs <;> norm_num))
  have hw : (∑ j : Fin (baseSegments b).length,
      (if j.val < b.upper.length then (2:ℝ) else 1)*
        ∫ u,W (z:ℝ) b.data.dual.σ u ∂((baseSegments b)[j]).measure)=
      ∫ u,W (z:ℝ) b.data.dual.σ u ∂b.data.dual.σ := by
    rw [integral_bent_sources b _ hW (bent_W_conj (z:ℝ) b hp)]
    calc
      _ = ∑ j : Fin (b.upper.length+b.atoms.length),
          (if j.val < b.upper.length then (2:ℝ) else 1)*
            ∫ u,W (z:ℝ) b.data.dual.σ u ∂(b.upper++b.atoms)[j].measure := by
        apply Fintype.sum_equiv (finCongr (show (baseSegments b).length=b.upper.length+b.atoms.length from List.length_append))
        intro j
        rfl
      _ = _ := weighted_append_sum b.upper b.atoms (fun s => ∫ u,W (z:ℝ) b.data.dual.σ u ∂s.measure)
  rw [hw] at hsum
  change _ ≤ ∫ u,V (z:ℝ) u-2*U b.data.dual.σ u ∂b.data.dual.σ at hsum
  rw [integral_sub hV (hU.const_mul 2),integral_const_mul] at hsum
  change (∫ u,U b.data.dual.σ u ∂b.data.dual.σ) ≤ _
  dsimp only [low] at hsum
  linarith

#print axioms energy_up_bent_labelled
end
end CatalanCore.Li2.DecayCert
