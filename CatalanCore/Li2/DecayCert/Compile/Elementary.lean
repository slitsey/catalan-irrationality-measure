module
public import CatalanCore.Li2.DecayCert.Compile.Own
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem ModelsOn.constant (c lo hi : ℝ) (hdom : lo ≤ hi) :
    ModelsOn (fun _ => c) [c] lo hi 0 := by
  refine ⟨hdom,le_rfl,?_⟩
  intro u hu
  simp [evalModel]

theorem ModelsOn.linear (a b lo hi : ℝ) (hdom : lo ≤ hi) :
    ModelsOn (fun u => a+b*u) [a,b] lo hi 0 := by
  refine ⟨hdom,le_rfl,?_⟩
  intro u hu
  rw [evalModel_pair,sub_self,abs_zero]

theorem fre_seed_value (b : CQ) (hb : cqReal b ≠ 0) (u : ℝ) (hu : 0 ≤ u) :
    (CellExpr.fre (0,0) b).value u = (b.1:ℝ)*xlog u+
      ((cqReal b*Complex.log (cqReal b)).re-(b.1:ℝ))*u := by
  by_cases hzero : u=0
  · subst u
    simp [CellExpr.value,cqReal,xlog]
  · have hp : 0 < u := lt_of_le_of_ne hu (Ne.symm hzero)
    have hz : cqReal (0,0)=(0:ℂ) := by simp [cqReal]
    simp only [CellExpr.value,hz,zero_add,Complex.log_mul_ofReal u hp _ hb]
    simp only [Complex.sub_re,mul_add,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    simp only [cqReal_re,cqReal_im,Complex.log_re,Complex.log_im,xlog]
    ring

theorem xlog_seed_value (b : ℚ) (hb : 0 < b) (u : ℝ) (hu : 0 ≤ u) :
    (CellExpr.xlog 0 b).value u=(b:ℝ)*xlog u+(b:ℝ)*Real.log (b:ℝ)*u := by
  have hbR : 0 < (b:ℝ) := by exact_mod_cast hb
  by_cases hz : u=0
  · subst u; simp [CellExpr.value,xlog]
  · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    simp only [CellExpr.value,Rat.cast_zero,zero_add,xlog,Real.log_mul hbR.ne' hu'.ne']
    ring

theorem fre_seed_model (b : CQ) (hb : cqReal b ≠ 0) (hi : ℚ) (hhi : 0 < hi) (terms : ℕ) :
    let m := ulogCompile hi terms
    ModelsOn (CellExpr.fre (0,0) b).value
      ((combineCoeffs (m.coeff.map (seScale b.1))
        [seRat 0,seSub (seReMulLog terms b b) (seRat b.1)]).map ScalarExpr.value)
      0 hi (|(b.1:ℝ)| *m.error.value) := by
  let C : ℝ := (cqReal b*Complex.log (cqReal b)).re-(b.1:ℝ)
  have hdom : (0:ℝ) ≤ (hi:ℝ) := by exact_mod_cast hhi.le
  have hl : ModelsOn (fun u => C*u)
      ([seRat 0,seSub (seReMulLog terms b b) (seRat b.1)].map ScalarExpr.value) 0 hi 0 := by
    have hh := ModelsOn.linear 0 C 0 hi hdom
    simpa only [List.map_cons,List.map_nil,seRat_value,seSub_value,seReMulLog_value,
      Rat.cast_zero,zero_add] using hh
  have hm := ((ulogCompile_sound hi hhi terms).scale_scalar b.1).add_scalar hl
  refine ⟨hm.1,?_,?_⟩
  · simpa only [add_zero] using hm.2.1
  · intro u hu
    have hh := hm.2.2 u hu
    rw [fre_seed_value b hb u hu.1]
    simpa only [add_zero] using hh

theorem xlog_seed_model (b hi : ℚ) (hb : 0 < b) (hhi : 0 < hi) (terms : ℕ) :
    let m := ulogCompile hi terms
    ModelsOn (CellExpr.xlog 0 b).value
      ((combineCoeffs (m.coeff.map (seScale b)) [seRat 0,seScale b (.log terms b)]).map ScalarExpr.value)
      0 hi ((b:ℝ)*m.error.value) := by
  have hbR : 0 ≤ (b:ℝ) := by exact_mod_cast hb.le
  have hdom : (0:ℝ) ≤ (hi:ℝ) := by exact_mod_cast hhi.le
  have hl : ModelsOn (fun u => (b:ℝ)*Real.log (b:ℝ)*u)
      ([seRat 0,seScale b (.log terms b)].map ScalarExpr.value) 0 hi 0 := by
    have hh := ModelsOn.linear 0 ((b:ℝ)*Real.log (b:ℝ)) 0 hi hdom
    simpa only [List.map_cons,List.map_nil,seRat_value,seScale_value,ScalarExpr.value,
      Rat.cast_zero,zero_add] using hh
  have hm := ((ulogCompile_sound hi hhi terms).scale_scalar b).add_scalar hl
  refine ⟨hm.1,?_,?_⟩
  · simpa only [abs_of_nonneg hbR,add_zero] using hm.2.1
  · intro u hu
    have hh := hm.2.2 u hu
    rw [xlog_seed_value b hb u hu.1]
    simpa only [abs_of_nonneg hbR,add_zero] using hh

theorem polynomial_compile_model (a : List ℚ) (lo hi : ℚ) (J : ℕ) (hdom : lo ≤ hi) :
    ModelsOn (CellExpr.poly a).value
      (((List.range (J+1)).map (fun j : ℕ => seRat (coeffQ a j))).map ScalarExpr.value) lo hi
      (((List.range a.length).map (fun j : ℕ =>
        if J < j then |coeffQ a j| *(max |lo| |hi|)^j else 0)).sum:ℚ) := by
  by_cases ha : a=[]
  · subst a
    refine ⟨by exact_mod_cast hdom,?_,?_⟩
    · simp
    · intro u hu
      have hz (j : ℕ) : coeffQ ([]:List ℚ) j=0 := by simp [coeffQ]
      simp only [CellExpr.value,List.length_nil,Finset.range_zero,Finset.sum_empty,
        List.range_zero,List.map_nil,List.sum_nil,Rat.cast_zero,hz]
      rw [List.map_map,evalModel_range]
      simp only [Function.comp_apply,seRat_value,Rat.cast_zero,zero_mul,Finset.sum_const_zero,
        sub_zero,abs_zero,le_refl]
  let pr : ℝ[X] := (qListPoly a).map (Rat.castHom ℝ)
  have hlen : a.length-1+1=a.length := by have := List.length_pos_iff.mpr ha; omega
  have hdeg : pr.natDegree ≤ a.length-1 := by
    change ((qListPoly a).map (Rat.castHom ℝ)).natDegree ≤ a.length-1
    have hnat := Polynomial.natDegree_map_le (p := qListPoly a) (f := Rat.castHom ℝ)
    have hlt := qListPoly_natDegree_lt a ha
    omega
  have hcoeff (j : ℕ) : pr.coeff j=(coeffQ a j:ℝ) := by simp [pr,Polynomial.coeff_map,qListPoly_coeff]
  have heval (u : ℝ) : pr.eval u=(CellExpr.poly a).value u := by
    simp [pr,qListPoly,Polynomial.map_sum,Polynomial.eval_finsetSum,CellExpr.value]
  have hm (u : ℝ) : evalModel
      (((List.range (J+1)).map (fun j : ℕ => seRat (coeffQ a j))).map ScalarExpr.value) u =
      ∑ j ∈ Finset.range (J+1),pr.coeff j*u^j := by
    rw [List.map_map,evalModel_range]
    simp only [Function.comp_apply,seRat_value,hcoeff]
  have herr : (((List.range a.length).map (fun j : ℕ =>
        if J < j then |coeffQ a j| *(max |lo| |hi|)^j else 0)).sum:ℚ) =
      ∑ j ∈ Finset.range a.length, if J < j then
        |pr.coeff j| *(max |(lo:ℝ)| |(hi:ℝ)|)^j else 0 := by
    rw [list_sum_map_range]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hJ : J < j
    · simp only [if_pos hJ,Rat.cast_mul,Rat.cast_abs,Rat.cast_pow,Rat.cast_max,hcoeff]
    · simp only [if_neg hJ,Rat.cast_zero]
  refine ⟨by exact_mod_cast hdom,?_,?_⟩
  · rw [herr]
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> positivity
  · intro u hu
    rw [← heval u,hm,herr]
    have hh := polynomial_truncation_bound_range pr J (a.length-1) hdeg _ _ u hu
    rwa [hlen] at hh

#print axioms xlog_seed_model
#print axioms polynomial_compile_model

#print axioms ModelsOn.constant
#print axioms ModelsOn.linear
#print axioms fre_seed_value
#print axioms xlog_seed_value
#print axioms fre_seed_model
end
end CatalanCore.Li2.DecayCert
