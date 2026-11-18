module
public import CatalanCore.Li2.DecayCert.Lines.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem LineCell.support_forward (c : LineCell) (hc : c.dir=1) :
    c.support=Icc (c.start:ℝ) ((c.start:ℝ)+(c.len:ℝ)) := by
  ext x
  simp only [LineCell.support,hc,Rat.cast_one,one_mul,mem_image,mem_Icc]
  constructor
  · rintro ⟨u,⟨hu0,huR⟩,rfl⟩; constructor <;> linarith
  · intro hx; exact ⟨x-c.start,⟨by linarith [hx.1],by linarith [hx.2]⟩,by ring⟩

theorem LineCell.support_backward (c : LineCell) (hc : c.dir= -1) :
    c.support=Icc ((c.start:ℝ)-(c.len:ℝ)) (c.start:ℝ) := by
  ext x
  simp only [LineCell.support,hc,Rat.cast_neg,Rat.cast_one,neg_one_mul,mem_image,mem_Icc]
  constructor
  · rintro ⟨u,⟨hu0,huR⟩,rfl⟩; constructor <;> linarith
  · intro hx; exact ⟨c.start-x,⟨by linarith [hx.2],by linarith [hx.1]⟩,by ring⟩

theorem LineCell.measurable_support (c : LineCell) : MeasurableSet c.support := by
  rcases c.direction with hc | hc
  · rw [c.support_forward hc]; exact measurableSet_Icc
  · rw [c.support_backward hc]; exact measurableSet_Icc

theorem LineCell.integral_support (c : LineCell) (f : ℝ → ℝ) :
    (∫ x in c.support,f x)=∫ u in (0:ℝ)..(c.len:ℝ),f ((c.start:ℝ)+(c.dir:ℝ)*u) := by
  have hl : (0:ℝ) ≤ (c.len:ℝ) := by exact_mod_cast c.len_nonneg
  rcases c.direction with hc | hc
  · rw [c.support_forward hc]
    simp only [hc,Rat.cast_one,one_mul]
    rw [intervalIntegral.integral_comp_add_left]
    simp only [add_zero]
    rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
  · rw [c.support_backward hc]
    have he := intervalIntegral.integral_comp_add_mul (a:=(0:ℝ)) (b:=(c.len:ℝ)) f (c:=(-1:ℝ)) (by norm_num) (c.start:ℝ)
    simp only [inv_neg,inv_one,neg_smul,one_smul,mul_zero,add_zero,neg_one_mul] at he
    rw [intervalIntegral.integral_symm (c.start+ -c.len:ℝ) (c.start:ℝ)] at he
    simp only [neg_neg] at he
    simp only [hc,Rat.cast_neg,Rat.cast_one,neg_one_mul]
    rw [he,intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
    congr 2 <;> ring

theorem LinePartition.integral_sum {α β : ℝ} (C : LinePartition α β)
    (hab : α ≤ β) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc α β)) :
    (∫ x in α..β,f x)=(C.cells.map (fun c => ∫ u in (0:ℝ)..(c.len:ℝ),f ((c.start:ℝ)+(c.dir:ℝ)*u))).sum := by
  classical
  have hu : (⋃ i : C.cells.toFinset,(i:LineCell).support)=Icc α β := by
    rw [← C.cover]
    ext x
    simp
  have hi : IntegrableOn f (Icc α β) := hf.integrableOn_Icc
  have hsum := integral_iUnion_ae (μ:=volume) (f:=f)
    (s:=fun i : C.cells.toFinset => (i:LineCell).support)
    (fun i => i.val.measurable_support.nullMeasurableSet)
    (fun i j hij => show AEDisjoint volume i.val.support j.val.support from
      C.overlap_null i.val (List.mem_toFinset.mp i.property) j.val (List.mem_toFinset.mp j.property)
        (by intro he; exact hij (Subtype.ext he))) (by rwa [hu])
  rw [hu,tsum_fintype,Finset.sum_coe_sort C.cells.toFinset (fun c : LineCell => ∫ x in c.support,f x)] at hsum
  rw [intervalIntegral.integral_of_le hab,← integral_Icc_eq_integral_Ioc,hsum]
  rw [← List.sum_toFinset _ C.nodup]
  congr 1
  funext c
  exact c.integral_support f

theorem Dsum_spec_real (f : ℝ → ℝ) (cells : LinePartition 1 4)
    (hf : ContinuousOn f (Icc 1 4))
    (hline : ∀ c ∈ cells.cells,∀ u ∈ Icc 0 (c.len:ℝ),
      f ((c.start:ℝ)+(c.dir:ℝ)*u) ≤ (c.a:ℝ)+(c.b:ℝ)*u) (ρ lam : ℝ) :
    (∫ x in (1:ℝ)..4,pos (f x-ρ-lam)) ≤ cells.posSum ρ lam := by
  have hf' : ContinuousOn (fun x => pos (f x-ρ-lam)) (Icc 1 4) := by
    unfold pos
    fun_prop
  rw [cells.integral_sum (by norm_num) _ hf']
  unfold LinePartition.posSum
  classical
  rw [← List.sum_toFinset _ cells.nodup,← List.sum_toFinset _ cells.nodup]
  apply Finset.sum_le_sum
  intro c hc
  have hc := List.mem_toFinset.mp hc
  rw [← int_pos_line_cell_real c.a c.b c.len (ρ+lam) (by exact_mod_cast c.len_nonneg)]
  have hsub : ∀ u ∈ Icc 0 (c.len:ℝ),(c.start:ℝ)+(c.dir:ℝ)*u ∈ Icc 1 4 := by
    intro u hu
    rw [← cells.cover]
    exact mem_iUnion.2 ⟨c,mem_iUnion.2 ⟨hc,⟨u,hu,rfl⟩⟩⟩
  have hccont : ContinuousOn (fun u => pos (f ((c.start:ℝ)+(c.dir:ℝ)*u)-ρ-lam)) (Icc 0 (c.len:ℝ)) :=
    hf'.comp (by fun_prop) hsub
  have hrcont : Continuous (fun u : ℝ => pos ((c.a:ℝ)+(c.b:ℝ)*u-(ρ+lam))) := by unfold pos; fun_prop
  apply intervalIntegral.integral_mono_on (by exact_mod_cast c.len_nonneg)
    (hccont.intervalIntegrable_of_Icc (by exact_mod_cast c.len_nonneg)) (hrcont.intervalIntegrable _ _)
  intro u hu
  apply max_le_max_right
  have hh := hline c hc u hu
  linarith
theorem Dsum_spec (f : ℝ → ℝ) (cells : LinePartition 1 4)
    (hf : ContinuousOn f (Icc 1 4))
    (hline : ∀ c ∈ cells.cells,∀ u ∈ Icc 0 (c.len:ℝ),
      f ((c.start:ℝ)+(c.dir:ℝ)*u) ≤ (c.a:ℝ)+(c.b:ℝ)*u) (ρ lam : ℚ) :
    (∫ x in (1:ℝ)..4,pos (f x-(ρ:ℝ)-(lam:ℝ))) ≤ (cells.posSumQ ρ lam:ℝ) := by
  rw [posSum_cast]
  exact Dsum_spec_real f cells hf hline ρ lam
#print axioms Dsum_spec
#print axioms LineCell.support_forward
#print axioms LineCell.support_backward
#print axioms LineCell.integral_support
#print axioms LinePartition.integral_sum
#print axioms Dsum_spec_real
end
end CatalanCore.Li2.DecayCert
