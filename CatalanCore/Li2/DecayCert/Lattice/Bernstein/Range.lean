module
public import CatalanCore.Li2.DecayCert.Density.Base
public import CatalanCore.Li2.DecayCert.PolynomialList
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set
open scoped BigOperators
open CatalanCore.Uniform.Decay.Tools
namespace CatalanCore.Li2.DecayCert
noncomputable section

def BoxRep (a : List ℚ) (bs : List (ℚ×ℚ)) : Prop :=
  bs.length=a.length ∧ ∀ k<a.length,
    (bs[k]?.getD (0,0)).1≤bernCoeff (qListPoly a) (-1) 1 (a.length-1) k ∧
    bernCoeff (qListPoly a) (-1) 1 (a.length-1) k≤(bs[k]?.getD (0,0)).2

theorem normalized_polynomial_bounds (a : List ℚ) (bs : List (ℚ×ℚ))
    (lo hi : ℚ) (hb : BoxRep a bs) (hne : a≠[])
    (hl : ∀ b∈bs, lo≤b.1) (hu : ∀ b∈bs, b.2≤hi) :
    ∀ t∈Icc (-1:ℝ) 1,
      (lo:ℝ)≤evalModel (a.map (fun q : ℚ => (q:ℝ))) t ∧
      evalModel (a.map (fun q : ℚ => (q:ℝ))) t≤(hi:ℝ) := by
  have ha : 0<a.length := by cases a <;> simp_all
  have hN : a.length-1+1=a.length := by omega
  have hmem (k : ℕ) (hk : k≤a.length-1) : bs[k]?.getD (0,0)∈bs := by
    have hk' : k<bs.length := by rw [hb.1]; omega
    simpa only [List.getElem?_eq_getElem hk',Option.getD_some] using List.getElem_mem hk'
  have hlo (k : ℕ) (hk : k≤a.length-1) :
      (lo:ℝ)≤bern (affCoeffs (fun j => ((qListPoly a).coeff j:ℝ))
        (a.length-1) (-1) 2) (a.length-1) k := by
    have hr : lo≤bernCoeff (qListPoly a) (-1) 1 (a.length-1) k :=
      (hl _ (hmem k hk)).trans (hb.2 k (by omega)).1
    have he := cast_bernCoeff (qListPoly a) (-1) 1 (a.length-1) k
    norm_num only [Rat.cast_neg,Rat.cast_one,sub_neg_eq_add,one_add_one_eq_two] at he
    rw [← he]
    exact_mod_cast hr
  have hhi (k : ℕ) (hk : k≤a.length-1) :
      bern (affCoeffs (fun j => ((qListPoly a).coeff j:ℝ))
        (a.length-1) (-1) 2) (a.length-1) k≤(hi:ℝ) := by
    have hr : bernCoeff (qListPoly a) (-1) 1 (a.length-1) k≤hi :=
      (hb.2 k (by omega)).2.trans (hu _ (hmem k hk))
    have he := cast_bernCoeff (qListPoly a) (-1) 1 (a.length-1) k
    norm_num only [Rat.cast_neg,Rat.cast_one,sub_neg_eq_add,one_add_one_eq_two] at he
    rw [← he]
    exact_mod_cast hr
  intro t ht
  have h := bernstein_range_Icc (fun j => ((qListPoly a).coeff j:ℝ))
    (a.length-1) (-1) 2 (by norm_num) hlo hhi ht.1 (by linarith [ht.2])
  simpa only [peval,hN,qListPoly_coeff,evalModel_map_rat] using h

theorem normalized_model_bounds (f : ℝ→ℝ) (a : List ℚ)
    (bs : List (ℚ×ℚ)) (E lo hi : ℚ)
    (hm : ModelsOn f (a.map (fun q : ℚ => (q:ℝ))) (-1) 1 E)
    (hb : BoxRep a bs) (hne : a≠[])
    (hl : ∀ b∈bs, lo≤b.1) (hu : ∀ b∈bs, b.2≤hi) :
    ∀ t∈Icc (-1:ℝ) 1, ((lo-E:ℚ):ℝ)≤f t ∧ f t≤((hi+E:ℚ):ℝ) := by
  intro t ht
  have hp := normalized_polynomial_bounds a bs lo hi hb hne hl hu t ht
  have he := abs_le.mp (hm.2.2 t ht)
  constructor <;> push_cast <;> linarith

theorem normalized_parent_bounds (f : ℝ→ℝ) (p r : ℝ) (hr : 0<r)
    (a : List ℚ) (bs : List (ℚ×ℚ)) (E lo hi : ℚ)
    (hm : ModelsOn (fun t => f (p+r*t)) (a.map (fun q : ℚ => (q:ℝ))) (-1) 1 E)
    (hb : BoxRep a bs) (hne : a≠[])
    (hl : ∀ b∈bs, lo≤b.1) (hu : ∀ b∈bs, b.2≤hi) :
    ∀ x∈Icc (p-r) (p+r), ((lo-E:ℚ):ℝ)≤f x ∧ f x≤((hi+E:ℚ):ℝ) := by
  intro x hx
  have ht : (x-p)/r∈Icc (-1:ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hr).2; linarith [hx.1]
    · apply (div_le_iff₀ hr).2; linarith [hx.2]
  have h := normalized_model_bounds (fun t => f (p+r*t)) a bs E lo hi hm hb hne hl hu _ ht
  have he : p+r*((x-p)/r)=x := by field_simp <;> ring
  simpa only [he] using h

#print axioms normalized_polynomial_bounds
#print axioms normalized_model_bounds
#print axioms normalized_parent_bounds
end
end CatalanCore.Li2.DecayCert
