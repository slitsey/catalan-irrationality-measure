module
public import CatalanCore.Li2.DecayCert.Bent.Expressions
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential
noncomputable section

theorem option_mapM_input {α β : Type*} (xs : List α) (f : α → Option β) :
    ∀ ys : List β,xs.mapM f=some ys → ∀ x ∈ xs,∃ y,f x=some y := by
  induction xs with
  | nil => intro ys hm x hx; simp at hx
  | cons a xs ih =>
    intro ys hm x hx
    cases ha : f a with
    | none => simp [ha] at hm
    | some b =>
      cases ht : xs.mapM f with
      | none => simp [ha,ht] at hm
      | some bs =>
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b,ha⟩
        · exact ih bs ht x hx

theorem sourceParameter_image_mass (s : QSegment) (hh : cqReal s.half ≠ 0) (a b : ℝ) :
    s.measure ((fun x : ℝ => cqReal s.mid+cqReal s.half*(x:ℂ)) '' Icc a b)=s.parameterMeasure (Icc a b) := by
  have hm : MeasurableSet ((fun x : ℝ => cqReal s.mid+cqReal s.half*(x:ℂ)) '' Icc a b) :=
    (isCompact_Icc.image (show Continuous (fun x : ℝ => cqReal s.mid+cqReal s.half*(x:ℂ)) by fun_prop)).measurableSet
  rw [← sourceParameter_map s,Measure.map_apply (by fun_prop) hm]
  congr 1
  ext x
  constructor
  · rintro ⟨y,hy,he⟩
    have heq : y=x := Complex.ofReal_inj.mp (mul_left_cancel₀ hh (add_left_cancel he))
    simpa only [heq] using hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem arcMassExpr_parameter (terms : ℕ) (s : QSegment) (a b : ArcPoint)
    (hh : cqReal s.half ≠ 0)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) x)
    (ha : a.valid=true) (hb : b.valid=true) (hab : a.x ≤ b.x) :
    (arcMassExpr terms s a b).value=s.parameterMeasure.real (Icc (a.x:ℝ) (b.x:ℝ)) := by
  rw [← arcMassExpr_real terms s a b hh hpos ha hb hab]
  exact congrArg ENNReal.toReal (sourceParameter_image_mass s hh (a.x:ℝ) (b.x:ℝ))

theorem energyCoverCheck_piece (b : BentInput) (es : List EnergyPiece) (hc : energyCoverCheck b es=true)
    (e : EnergyPiece) (he : e ∈ es) :
    e.segment < (baseSegments b).length ∧ e.left.valid=true ∧ e.right.valid=true ∧ e.left.x < e.right.x := by
  have h := hc
  simp only [energyCoverCheck,Bool.and_eq_true] at h
  have hr := (List.all_eq_true.mp h.1) e he
  simp only [Bool.and_eq_true] at hr
  have hseg := (of_decide_eq_true hr.1.1).1
  refine ⟨hseg,hr.1.2,hr.2,?_⟩
  let selected := es.filter (fun q => q.segment==e.segment)
  let intervals := selected.map (fun q : EnergyPiece => (⟨q.left.x,q.right.x⟩:QInterval))
  have hchain : chainCheck (-1) 1 intervals=true :=
    (List.all_eq_true.mp h.2) e.segment (List.mem_range.mpr hseg)
  have hem : (⟨e.left.x,e.right.x⟩:QInterval) ∈ intervals := by
    apply List.mem_map.mpr
    exact ⟨e,List.mem_filter.mpr ⟨he,by simp⟩,rfl⟩
  exact ((chainCheck_sound (-1) 1 intervals hchain).2.2.1 _ hem).2.1

theorem labelled_sum_reindex {m n : ℕ} (label : Fin m → ℕ) (hl : ∀ i,label i < n)
    (w : Fin n → ℝ) (f : Fin n → Fin m → ℝ) :
    (∑ i,w ⟨label i,hl i⟩*f ⟨label i,hl i⟩ i)=
      ∑ j,w j*∑ i,if label i=j.val then f j i else 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  symm
  rw [Finset.sum_eq_single (⟨label i,hl i⟩:Fin n)]
  · simp only [ite_true]
  · intro j hj hne
    have hlabel : label i ≠ j.val := by
      intro he
      apply hne
      exact Fin.ext he.symm
    simp only [if_neg hlabel,mul_zero]
  · simp
#print axioms option_mapM_input
#print axioms sourceParameter_image_mass
#print axioms arcMassExpr_parameter
#print axioms energyCoverCheck_piece
#print axioms labelled_sum_reindex
end
end CatalanCore.Li2.DecayCert
