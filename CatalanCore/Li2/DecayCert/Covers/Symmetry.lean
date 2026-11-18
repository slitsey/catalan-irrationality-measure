module
public import CatalanCore.Li2.DecayCert.Covers.Placement
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem QSegment.conj_conj (s : QSegment) : s.conj.conj=s := by
  rcases s with ⟨⟨mr,mi⟩,⟨hr,hi⟩,co⟩
  simp [QSegment.conj]

theorem QSegment.conj_measure (s : QSegment) :
    s.conj.measure=s.measure.map (starRingEnd ℂ) := by
  have h := CatalanCore.Lai.DecayEnergy.map_conj_segMeasure (cqReal s.mid) (cqReal s.half)
    (fun k => (s.c k:ℝ)) (s.coeff.length-1)
  simpa [QSegment.measure,QSegment.conj,QSegment.c,cqReal] using h.symm

theorem map_conj_sourceSum (ss : List QSegment) :
    ((ss.map QSegment.measure).sum).map (starRingEnd ℂ)=((ss.map QSegment.conj).map QSegment.measure).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons,List.sum_cons,Measure.map_add _ _ Complex.continuous_conj.measurable,ih]
    rw [← QSegment.conj_measure]

theorem QSegment.conj_eq_of_real (s : QSegment) (hm : s.mid.2=0) (hh : s.half.2=0) : s.conj=s := by
  rcases s with ⟨⟨mr,mi⟩,⟨hr,hi⟩,co⟩
  dsimp only at hm hh
  subst mi
  subst hi
  simp [QSegment.conj]

theorem bent_measure_conj (b : BentInput) (hp : placementCheck b=true) :
    b.data.dual.σ.map (starRingEnd ℂ)=b.data.dual.σ := by
  have hσ : b.data.dual.σ=(b.upper.map QSegment.measure).sum+
      ((b.upper.map QSegment.conj).map QSegment.measure).sum+(b.atoms.map QSegment.measure).sum := by
    rw [b.data.measure_eq,b.source_eq]
    simp only [List.map_append,List.sum_append]
  have hupper : (b.upper.map QSegment.conj).map QSegment.conj=b.upper := by
    simp only [List.map_map,Function.comp_def,QSegment.conj_conj]
    exact List.map_id _
  have hatoms : b.atoms.map QSegment.conj=b.atoms := by
    calc
      _ = b.atoms.map id := by
        apply List.map_congr_left
        intro s hs
        have ha := placementCheck_atom b hp s hs
        exact s.conj_eq_of_real ha.1 ha.2.1
      _ = _ := List.map_id _
  rw [hσ,Measure.map_add _ _ Complex.continuous_conj.measurable,
    Measure.map_add _ _ Complex.continuous_conj.measurable,map_conj_sourceSum,map_conj_sourceSum,map_conj_sourceSum,hupper,hatoms]
  abel

theorem phi0_conj (u : ℂ) : phi0 (starRingEnd ℂ u)=phi0 u := by
  have hn (x : ℝ) : ‖starRingEnd ℂ u+(x:ℂ)‖=‖u+(x:ℂ)‖ := by
    rw [← Complex.norm_conj (u+(x:ℂ))]
    congr 1
    simp
  change 3*(∫ x in (0:ℝ)..1,Real.log ‖starRingEnd ℂ u+(x:ℂ)‖)-
      (∫ x in (0:ℝ)..4,Real.log ‖starRingEnd ℂ u+(x:ℂ)‖)=_
  simp only [hn]
  rfl

theorem V_conj (z : ℝ) (u : ℂ) : V z (starRingEnd ℂ u)=V z u := by
  simp only [V,phi0_conj,Complex.conj_re,Complex.conj_im,abs_neg]

theorem bent_P_conj (b : BentInput) (hp : placementCheck b=true) (u : ℂ) :
    P b.data.dual.σ (starRingEnd ℂ u)=P b.data.dual.σ u := by
  have h := CatalanCore.Lai.DecayEnergy.potC_conj_arg b.data.dual.σ u
  rw [bent_measure_conj b hp] at h
  exact h

theorem bent_W_conj (z : ℝ) (b : BentInput) (hp : placementCheck b=true) (u : ℂ) :
    W z b.data.dual.σ (starRingEnd ℂ u)=W z b.data.dual.σ u := by
  rw [W,W,V_conj,U,U,bent_P_conj b hp]

theorem integral_conj_source (s : QSegment) (f : ℂ → ℝ) (hf : ∀ u,f (starRingEnd ℂ u)=f u) :
    (∫ u,f u ∂s.conj.measure)=∫ u,f u ∂s.measure := by
  rw [s.conj_measure]
  have hm : MeasurableEmbedding (starRingEnd ℂ) := Complex.conjLIE.toHomeomorph.measurableEmbedding
  rw [hm.integral_map]
  simp only [hf]

theorem integral_source_sum (ss : List QSegment) (f : ℂ → ℝ)
    (hf : Integrable f (ss.map QSegment.measure).sum) :
    (∫ u,f u ∂(ss.map QSegment.measure).sum)=(ss.map (fun s => ∫ u,f u ∂s.measure)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons,List.sum_cons] at hf ⊢
    have hh := integrable_add_measure.mp hf
    rw [integral_add_measure hh.1 hh.2,ih hh.2]

theorem integral_bent_sources (b : BentInput) (f : ℂ → ℝ)
    (hf : Integrable f b.data.dual.σ) (hconj : ∀ u,f (starRingEnd ℂ u)=f u) :
    (∫ u,f u ∂b.data.dual.σ)=2*(b.upper.map (fun s => ∫ u,f u ∂s.measure)).sum+
      (b.atoms.map (fun s => ∫ u,f u ∂s.measure)).sum := by
  rw [b.data.measure_eq,b.source_eq] at hf ⊢
  rw [integral_source_sum _ f hf]
  simp only [List.map_append,List.sum_append,List.map_map]
  have hh : (b.upper.map (fun s => ∫ u,f u ∂s.conj.measure)).sum=
      (b.upper.map (fun s => ∫ u,f u ∂s.measure)).sum := by
    congr 1
    apply List.map_congr_left
    intro s hs
    exact integral_conj_source s f hconj
  simp only [Function.comp_def] at *
  rw [hh]
  ring
#print axioms QSegment.conj_measure
#print axioms bent_measure_conj
#print axioms phi0_conj
#print axioms V_conj
#print axioms bent_P_conj
#print axioms bent_W_conj
#print axioms integral_conj_source
#print axioms integral_source_sum
#print axioms integral_bent_sources
end
end CatalanCore.Li2.DecayCert
