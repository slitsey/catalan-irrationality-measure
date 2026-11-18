module
public import CatalanCore.Li2.DecayCert.Lattice.Bernstein.Source
public import CatalanCore.Li2.DecayCert.Lattice.Bernstein.Subdivision
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open Polynomial Set
open scoped BigOperators
open CatalanCore.Uniform.Decay.Tools
namespace CatalanCore.Li2.DecayCert.BernsteinGrid

def canonicalControls (p : ℚ[X]) (a b : ℚ) (n : ℕ) : List ℚ :=
  (List.range (n+1)).map (bernCoeff p a b n)

theorem canonicalControls_length (p : ℚ[X]) (a b : ℚ) (n : ℕ) :
    (canonicalControls p a b n).length=n+1 := by simp [canonicalControls]

theorem controlEval_eq_bezier (ys : List ℚ) (n : ℕ) (hn : ys.length=n+1) (t : ℚ) :
    controlEval ys t=bezier n (lget ys) t := by
  simp only [controlEval,bezier,hn,Nat.add_sub_cancel]

theorem controlEval_canonical (p : ℚ[X]) (a b : ℚ) (n : ℕ) (hn : p.natDegree≤n) (t : ℚ) :
    controlEval (canonicalControls p a b n) t=p.eval (a+(b-a)*t) := by
  unfold controlEval
  rw [canonicalControls_length]
  simp only [Nat.add_sub_cancel]
  calc
    _=∑ k ∈ Finset.range (n+1),bernCoeff p a b n k*bw n k t := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [canonicalControls,lget_map_range,if_pos (Finset.mem_range.mp hk)]
    _=_ := bernCoeff_eval p a b n hn t

theorem exactSplit_canonical (p : ℚ[X]) (a b : ℚ) (n : ℕ) (hn : p.natDegree≤n) :
    exactSplit (canonicalControls p a b n)=
      (canonicalControls p a ((a+b)/2) n,canonicalControls p ((a+b)/2) b n) := by
  have hl := canonicalControls_length p a b n
  have hs := exactSplitFuel_length (canonicalControls p a b n).length (canonicalControls p a b n)
  apply Prod.ext
  · apply controlEval_unique
    · simpa only [exactSplit,hl,canonicalControls_length] using hs.1
    · intro t
      rw [controlEval_eq_bezier _ n (by simpa only [exactSplit,hl] using hs.1),
        exactSplit_left_eval n _ hl,← controlEval_eq_bezier _ n hl,controlEval_canonical _ _ _ _ hn,
        controlEval_canonical _ _ _ _ hn]
      congr 1
      ring
  · apply controlEval_unique
    · simpa only [exactSplit,hl,canonicalControls_length] using hs.2
    · intro t
      rw [controlEval_eq_bezier _ n (by simpa only [exactSplit,hl] using hs.2),
        exactSplit_right_eval n _ hl,← controlEval_eq_bezier _ n hl,controlEval_canonical _ _ _ _ hn,
        controlEval_canonical _ _ _ _ hn]
      congr 1
      ring

theorem splitInts_canonical (S : ℤ) (hS : 0<S) (xs : List (ℤ×ℤ))
    (p : ℚ[X]) (a b : ℚ) (n : ℕ) (hn : p.natDegree≤n)
    (h : TableEncloses S xs (canonicalControls p a b n)) :
    TableEncloses S (splitInts xs).1 (canonicalControls p a ((a+b)/2) n) ∧
      TableEncloses S (splitInts xs).2 (canonicalControls p ((a+b)/2) b n) := by
  have hh := splitInts_sound S hS xs _ h
  rw [exactSplit_canonical p a b n hn] at hh
  exact hh

theorem bernInts_split_source (S A B D : ℤ) (hS : 0<S) (hD : 0<D)
    (cs : List ℤ) (hne : cs≠[]) :
    let p := qListPoly (cs.map (fun c : ℤ => (c:ℚ)/(S:ℚ)))
    let a := (A:ℚ)/(D:ℚ)
    let b := (B:ℚ)/(D:ℚ)
    TableEncloses S (splitInts (bernInts A B D cs)).1
      (canonicalControls p a ((a+b)/2) (cs.length-1)) ∧
    TableEncloses S (splitInts (bernInts A B D cs)).2
      (canonicalControls p ((a+b)/2) b (cs.length-1)) := by
  dsimp only
  have hh := bernInts_sound S A B D hS hD cs
  rw [exactControls_bernCoeff S A B D hD.ne' cs hne] at hh
  have hl : cs.length=cs.length-1+1 := by cases cs <;>simp_all
  have hp := qListPoly_natDegree_lt (cs.map (fun c : ℤ => (c:ℚ)/(S:ℚ))) (by simpa using hne)
  apply splitInts_canonical S hS _ _ _ _ _ (by simp only [List.length_map] at hp;omega)
  simpa only [canonicalControls,← hl] using hh

/-- Source-polynomial box representation on any rational cell. -/
def CellBoxRep (p : ℚ[X]) (a b : ℚ) (n : ℕ) (bs : List (ℚ×ℚ)) : Prop :=
  bs.length=n+1 ∧ ∀ k≤n,
    (lget bs k).1≤bernCoeff p a b n k ∧ bernCoeff p a b n k≤(lget bs k).2

theorem tableEncloses_CellBoxRep (S : ℤ) (hS : 0<S) (xs : List (ℤ×ℤ))
    (p : ℚ[X]) (a b : ℚ) (n : ℕ)
    (h : TableEncloses S xs (canonicalControls p a b n)) :
    CellBoxRep p a b n (decodedBoxes S xs) := by
  have hs : (0:ℚ)<(S:ℚ) := by exact_mod_cast hS
  refine ⟨by simpa only [decodedBoxes,List.length_map,canonicalControls_length] using h.1,?_⟩
  intro k hk
  have hh := h.2 k
  simp only [canonicalControls,lget_map_range,show k<n+1 by omega,ite_true] at hh
  rw [lget_decodedBoxes]
  exact ⟨(div_le_iff₀ hs).2 (by simpa only [mul_comm] using hh.1),
    (le_div_iff₀ hs).2 (by simpa only [mul_comm] using hh.2)⟩

theorem cell_polynomial_bounds (p : ℚ[X]) (a b lo hi : ℚ) (n : ℕ)
    (hn : p.natDegree≤n) (hab : a≤b) (bs : List (ℚ×ℚ))
    (hb : CellBoxRep p a b n bs)
    (hl : ∀ c∈bs,lo≤c.1) (hu : ∀ c∈bs,c.2≤hi) :
    ∀ x∈Icc (a:ℝ) (b:ℝ), (lo:ℝ)≤(p.map (Rat.castHom ℝ)).eval x ∧
      (p.map (Rat.castHom ℝ)).eval x≤(hi:ℝ) := by
  have hm (k : ℕ) (hk : k≤n) : lget bs k∈bs := by
    have hk' : k<bs.length := by rw [hb.1];omega
    simpa only [lget,List.getElem?_eq_getElem hk',Option.getD_some] using List.getElem_mem hk'
  have hlo (k : ℕ) (hk : k≤n) : (lo:ℝ)≤
      bern (affCoeffs (fun j=>(p.coeff j:ℝ)) n (a:ℝ) ((b:ℝ)-a)) n k := by
    rw [← cast_bernCoeff]
    exact_mod_cast (hl _ (hm k hk)).trans (hb.2 k hk).1
  have hhi (k : ℕ) (hk : k≤n) :
      bern (affCoeffs (fun j=>(p.coeff j:ℝ)) n (a:ℝ) ((b:ℝ)-a)) n k≤(hi:ℝ) := by
    rw [← cast_bernCoeff]
    exact_mod_cast (hb.2 k hk).2.trans (hu _ (hm k hk))
  intro x hx
  have he : (p.map (Rat.castHom ℝ)).eval x=peval (fun j=>(p.coeff j:ℝ)) n x := by
    rw [Polynomial.eval_map,Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ) (by omega : p.natDegree<n+1)]
    rfl
  rw [he]
  obtain ⟨t,ht0,ht1,ht⟩ : ∃t:ℝ,0≤t ∧ t≤1 ∧ (a:ℝ)+((b:ℝ)-a)*t=x := by
    by_cases hab' : (a:ℝ)<(b:ℝ)
    · refine ⟨(x-a)/(b-a),div_nonneg (by linarith [hx.1]) (by linarith),?_,?_⟩
      · apply (div_le_one (by linarith : (0:ℝ)<b-a)).2
        linarith [hx.2]
      · have hd : (b:ℝ)-a≠0 := sub_ne_zero.mpr hab'.ne'
        field_simp [hd]
        <;> ring
    · refine ⟨0,le_rfl,zero_le_one,?_⟩
      have habR : (a:ℝ)≤(b:ℝ) := by exact_mod_cast hab
      simp only [mul_zero,add_zero]
      linarith [hx.1,hx.2]
  have hh := bernstein_range _ n hlo hhi ht0 ht1
  rw [peval_affCoeffs,ht] at hh
  exact hh

#print axioms exactSplit_canonical
#print axioms bernInts_split_source
#print axioms cell_polynomial_bounds
/-- Children reuse the parent's proved error; source preparation is not repeated. -/
theorem normalized_child_model_bounds (f : ℝ→ℝ) (a : List ℚ)
    (u v E lo hi : ℚ) (bs : List (ℚ×ℚ)) (hne : a≠[])
    (huv : u≤v) (hul : -1≤u) (hvu : v≤1)
    (hm : ModelsOn f (a.map (fun q : ℚ => (q:ℝ))) (-1) 1 E)
    (hb : CellBoxRep (qListPoly a) u v (a.length-1) bs)
    (hl : ∀ c∈bs,lo≤c.1) (hu : ∀ c∈bs,c.2≤hi) :
    ∀ x∈Icc (u:ℝ) (v:ℝ), ((lo-E:ℚ):ℝ)≤f x ∧ f x≤((hi+E:ℚ):ℝ) := by
  have hn := qListPoly_natDegree_lt a hne
  intro x hx
  have hp := cell_polynomial_bounds (qListPoly a) u v lo hi (a.length-1)
    (by omega) huv bs hb hl hu x hx
  have hev : ((qListPoly a).map (Rat.castHom ℝ)).eval x=
      evalModel (a.map (fun q : ℚ => (q:ℝ))) x := by
    rw [Polynomial.eval_map,Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ) hn]
    simp only [qListPoly_coeff,evalModel_map_rat]
    rfl
  rw [hev] at hp
  have hx' : x∈Icc (-1:ℝ) 1 := by
    have huR : (-1:ℝ)≤(u:ℝ) := by exact_mod_cast hul
    have hvR : (v:ℝ)≤1 := by exact_mod_cast hvu
    exact ⟨huR.trans hx.1,hx.2.trans hvR⟩
  have he := abs_le.mp (hm.2.2 x hx')
  constructor <;> push_cast <;> linarith

#print axioms normalized_child_model_bounds

end CatalanCore.Li2.DecayCert.BernsteinGrid
