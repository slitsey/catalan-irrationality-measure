module
public import CatalanCore.Li2.DecayCert.Lattice.Cells
public import CatalanCore.Li2.DecayCert.Lattice.Tail
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem chainCheck_integral_sum (a b : ℚ) (cs : List QInterval) (hc : chainCheck a b cs=true)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in (a:ℝ)..(b:ℝ),f x)=(cs.map (fun c => ∫ x in (c.left:ℝ)..(c.right:ℝ),f x)).sum := by
  induction cs generalizing a with
  | nil =>
    have he : a=b := of_decide_eq_true hc
    subst b
    simp
  | cons c cs ih =>
    simp only [chainCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
    rcases hc with ⟨⟨he,hlt,hle⟩,ht⟩
    simp only [List.map_cons,List.sum_cons]
    rw [he,← ih c.right ht]
    exact (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm

theorem list_sum_map_le_rat {α : Type*} (xs : List α) (f : α → ℝ) (g : α → ℚ) :
    (∀ x ∈ xs,f x ≤ (g x:ℝ)) → (xs.map f).sum ≤ (((xs.map g).sum:ℚ):ℝ) := by
  induction xs with
  | nil => intro h; simp
  | cons x xs ih =>
    intro h
    simp only [List.map_cons,List.sum_cons,Rat.cast_add]
    exact add_le_add (h x List.mem_cons_self) (ih (fun q hq => h q (List.mem_cons_of_mem x hq)))

theorem chainCheck_cells_integral_bound {α : Type*} (a b : ℚ) (cs : List α) (I : α → QInterval)
    (hc : chainCheck a b (cs.map I)=true) (f : ℝ → ℝ) (hf : Continuous f) (cap : α → ℚ)
    (hb : ∀ c ∈ cs,(∫ x in ((I c).left:ℝ)..((I c).right:ℝ),f x) ≤ (cap c:ℝ)) :
    (∫ x in (a:ℝ)..(b:ℝ),f x) ≤ (((cs.map cap).sum:ℚ):ℝ) := by
  have he := chainCheck_integral_sum a b (cs.map I) hc f hf
  simp only [List.map_map,Function.comp_def] at he
  rw [he]
  exact list_sum_map_le_rat cs _ cap hb

theorem integral_Ici_of_zero_tail (f : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ht : ∀ x : ℝ,C ≤ x → f x=0) :
    (∫ x in Ici (0:ℝ),f x)=∫ x in (0:ℝ)..C,f x := by
  have he : (Ici (0:ℝ)).indicator f=(Icc (0:ℝ) C).indicator f := by
    funext x
    by_cases h0 : 0 ≤ x
    · by_cases hx : x ≤ C
      · rw [indicator_of_mem (show x ∈ Ici (0:ℝ) from h0),indicator_of_mem (show x ∈ Icc (0:ℝ) C from ⟨h0,hx⟩)]
      · rw [indicator_of_mem (show x ∈ Ici (0:ℝ) from h0),indicator_of_notMem (show x ∉ Icc (0:ℝ) C by intro h; exact hx h.2),ht x (lt_of_not_ge hx).le]
    · rw [indicator_of_notMem (show x ∉ Ici (0:ℝ) from h0),indicator_of_notMem (show x ∉ Icc (0:ℝ) C by intro h; exact h0 h.1)]
  calc
    _ = ∫ x,(Ici (0:ℝ)).indicator f x := (integral_indicator measurableSet_Ici).symm
    _ = ∫ x,(Icc (0:ℝ) C).indicator f x := by rw [he]
    _ = ∫ x in Icc (0:ℝ) C,f x := integral_indicator measurableSet_Icc
    _ = _ := by rw [intervalIntegral.integral_of_le hC,integral_Icc_eq_integral_Ioc]
#print axioms chainCheck_integral_sum
#print axioms chainCheck_cells_integral_bound
#print axioms integral_Ici_of_zero_tail
end
end CatalanCore.Li2.DecayCert
