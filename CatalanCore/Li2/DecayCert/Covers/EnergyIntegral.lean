module
public import CatalanCore.Li2.DecayCert.Covers.EnergyPartition
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential
noncomputable section

theorem parameter_partition_lower {J : Type*} [Fintype J] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) (cells : J → Set ℝ) (lower : J → ℝ)
    (hmeas : ∀ j,MeasurableSet (cells j)) (hcover : μ (⋃ j,cells j)ᶜ=0)
    (hnull : ∀ j k,j ≠ k → μ (cells j ∩ cells k)=0)
    (hlo : ∀ j,∀ᵐ x ∂μ.restrict (cells j),lower j ≤ f x) :
    (∑ j,μ.real (cells j)*lower j) ≤ ∫ x,f x ∂μ := by
  classical
  have hr : μ.restrict (⋃ j,cells j)=μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hcover)
  have he := integral_iUnion_ae (μ:=μ) (f:=f) (fun j => (hmeas j).nullMeasurableSet) hnull hf.integrableOn
  rw [hr,tsum_fintype] at he
  rw [he]
  apply Finset.sum_le_sum
  intro j hj
  have h := integral_mono_ae (integrable_const (lower j)) hf.integrableOn (hlo j)
  simpa only [integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply MeasurableSet.univ,univ_inter] using h

theorem source_parameter_finite (s : QSegment) : IsFiniteMeasure s.parameterMeasure := by
  unfold QSegment.parameterMeasure
  haveI : IsFiniteMeasure (arc.withDensity (fun θ => ENNReal.ofReal
      (chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) (Real.cos θ)))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1)).2
  infer_instance

theorem source_parameter_integrable (s : QSegment) (f : ℂ → ℝ) (hf : Integrable f s.measure) :
    Integrable (fun x : ℝ => f (cqReal s.mid+cqReal s.half*(x:ℂ))) s.parameterMeasure := by
  have hf' : Integrable f (s.parameterMeasure.map (fun x : ℝ => cqReal s.mid+cqReal s.half*(x:ℂ))) := by
    rwa [sourceParameter_map]
  exact hf'.comp_aemeasurable (by fun_prop)

theorem source_parameter_integral (s : QSegment) (f : ℂ → ℝ) (hf : Integrable f s.measure) :
    (∫ x : ℝ,f (cqReal s.mid+cqReal s.half*(x:ℂ)) ∂s.parameterMeasure)=∫ z,f z ∂s.measure := by
  have hfm : AEStronglyMeasurable f (s.parameterMeasure.map (fun x : ℝ => cqReal s.mid+cqReal s.half*(x:ℂ))) := by
    rw [sourceParameter_map]
    exact hf.aestronglyMeasurable
  have h := integral_map (show AEMeasurable (fun x : ℝ => cqReal s.mid+cqReal s.half*(x:ℂ)) s.parameterMeasure by fun_prop) hfm
  rw [sourceParameter_map] at h
  exact h.symm

theorem source_measure_le_sum (ss : List QSegment) (s : QSegment) (hs : s ∈ ss) :
    s.measure ≤ (ss.map QSegment.measure).sum := by
  induction ss with
  | nil => simp at hs
  | cons t ss ih =>
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp hs with rfl | hs
    · exact le_add_of_nonneg_right (show (0:Measure ℂ) ≤ (ss.map QSegment.measure).sum from bot_le)
    · exact (ih hs).trans (le_add_of_nonneg_left (show (0:Measure ℂ) ≤ t.measure from bot_le))

theorem fin_sum_list_map {α : Type*} (xs : List α) (f : α → ℝ) :
    (∑ i : Fin xs.length,f xs[i])=(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    change (∑ i : Fin (xs.length+1),f (a::xs)[i])=_
    rw [Fin.sum_univ_succ]
    simpa only [Fin.getElem_fin,List.getElem_cons_zero,List.getElem_cons_succ,List.map_cons,List.sum_cons,Fin.val_zero,Fin.val_succ] using
      congrArg (fun x => f a+x) ih

theorem weighted_append_sum {α : Type*} (xs ys : List α) (f : α → ℝ) :
    (∑ i : Fin (xs.length+ys.length),(if i.val < xs.length then (2:ℝ) else 1)*f ((xs++ys)[i]))=
      2*(xs.map f).sum+(ys.map f).sum := by
  have hl (i : Fin xs.length) : (if (Fin.castAdd ys.length i).val < xs.length then (2:ℝ) else 1)*
      f ((xs++ys)[Fin.castAdd ys.length i])=2*f xs[i] := by
    simp [List.getElem_append_left,i.isLt]
  have hr (i : Fin ys.length) : (if (Fin.natAdd xs.length i).val < xs.length then (2:ℝ) else 1)*
      f ((xs++ys)[Fin.natAdd xs.length i])=f ys[i] := by
    simp [List.getElem_append_right,Nat.not_lt.mpr (Nat.le_add_right xs.length i.val)]
  rw [Fin.sum_univ_add]
  simp only [hl,hr]
  rw [← Finset.mul_sum,fin_sum_list_map,fin_sum_list_map]
#print axioms parameter_partition_lower
#print axioms source_parameter_finite
#print axioms source_parameter_integrable
#print axioms source_parameter_integral
#print axioms source_measure_le_sum
#print axioms fin_sum_list_map
#print axioms weighted_append_sum
end
end CatalanCore.Li2.DecayCert
