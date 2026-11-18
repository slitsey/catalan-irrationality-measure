module
public import CatalanCore.Li2.DecayCert.Compile.OwnBase
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem polynomial_truncation_bound_range (p : ℝ[X]) (J n : ℕ) (hn : p.natDegree ≤ n)
    (l r u : ℝ) (hu : u ∈ Icc l r) :
    |p.eval u-∑ j ∈ Finset.range (J+1),p.coeff j*u^j| ≤
      ∑ j ∈ Finset.range (n+1), if J < j then |p.coeff j| *(max |l| |r|)^j else 0 := by
  apply (polynomial_truncation_bound p J l r u hu).trans
  have hsum : (∑ j ∈ Finset.Icc (J+1) p.natDegree, |p.coeff j| *(max |l| |r|)^j) =
      ∑ j ∈ Finset.range (n+1), if j ∈ Finset.Icc (J+1) p.natDegree then
        |p.coeff j| *(max |l| |r|)^j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    omega
  rw [hsum]
  apply Finset.sum_le_sum
  intro j hj
  split_ifs with ha hb hb
  · exact le_rfl
  · simp only [Finset.mem_Icc] at ha
    omega
  · positivity
  · exact le_rfl

theorem real_affine_map (p : ℚ[X]) (x γ : CQ) (hx : x.2=0) (hγ : γ.2=0) :
    (((p.map (Rat.castHom ℝ)).comp (C (x.1:ℝ)+C (γ.1:ℝ)*X)).map Complex.ofRealHom) =
      (p.map (Rat.castHom ℂ)).comp (C (cqReal x)+C (cqReal γ)*X) := by
  simp only [Polynomial.map_comp,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_X,Polynomial.map_map]
  have hxR : cqReal x=((x.1:ℝ):ℂ) := by simp [cqReal,hx]
  have hγR : cqReal γ=((γ.1:ℝ):ℂ) := by simp [cqReal,hγ]
  rw [hxR,hγR]
  congr 2

theorem qShiftCoeff_real_spec (p : ℚ[X]) (x γ : CQ) (hx : x.2=0) (hγ : γ.2=0) (j : ℕ) :
    ((qShiftCoeff p x γ j).1:ℝ)=
      ((p.map (Rat.castHom ℝ)).comp (C (x.1:ℝ)+C (γ.1:ℝ)*X)).coeff j := by
  rw [← cqReal_re,qShiftCoeff_spec,← real_affine_map p x γ hx hγ,Polynomial.coeff_map]
  simp

theorem affine_natDegree_le (p : ℚ[X]) (x γ : ℝ) :
    ((p.map (Rat.castHom ℝ)).comp (C x+C γ*X)).natDegree ≤ p.natDegree := by
  have ha : (C x+C γ*X : ℝ[X]).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le γ 1
  calc
    _ ≤ (p.map (Rat.castHom ℝ)).natDegree*(C x+C γ*X : ℝ[X]).natDegree := Polynomial.natDegree_comp_le
    _ ≤ p.natDegree*1 := Nat.mul_le_mul (Polynomial.natDegree_map_le) ha
    _ = _ := Nat.mul_one _

theorem ownScalarCoeff_model (d : QSegment) (x γ : CQ) (terms J : ℕ) (u : ℝ) :
    evalModel (((List.range (J+1)).map (ownScalarCoeff d x γ terms)).map ScalarExpr.value) u =
      (∑ j ∈ Finset.range (J+1), ((qShiftCoeff d.ownPolyQ x γ j).1:ℝ)*u^j) +
        (d.c 0:ℝ)*(Real.log ‖cqReal d.half‖-Real.log 2) := by
  rw [List.map_map,evalModel_range]
  have hs (j : ℕ) : (ownScalarCoeff d x γ terms j).value*u^j =
      ((qShiftCoeff d.ownPolyQ x γ j).1:ℝ)*u^j +
        (if j=0 then (d.c 0:ℝ)*(Real.log ‖cqReal d.half‖-Real.log 2) else 0) := by
    by_cases hj : j=0
    · subst j
      rw [ownScalarCoeff_zero_value]
      simp
    · simp [ownScalarCoeff,hj,seRat_value]
  simp only [Function.comp_apply,hs,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_range]
  simp

theorem affine_interval_unit (x γ lo hi : ℝ)
    (hlo : -1 ≤ x+γ*lo ∧ x+γ*lo ≤ 1) (hhi : -1 ≤ x+γ*hi ∧ x+γ*hi ≤ 1)
    (u : ℝ) (hu : u ∈ Icc lo hi) : x+γ*u ∈ Icc (-1:ℝ) 1 := by
  by_cases hg : 0 ≤ γ
  · constructor
    · nlinarith [mul_nonneg hg (sub_nonneg.mpr hu.1)]
    · nlinarith [mul_nonneg hg (sub_nonneg.mpr hu.2)]
  · have hg' : γ ≤ 0 := le_of_not_ge hg
    constructor
    · nlinarith [mul_nonneg (neg_nonneg.mpr hg') (sub_nonneg.mpr hu.2)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hg') (sub_nonneg.mpr hu.1)]

theorem ownCompile_shape (d : QSegment) (p e : CQ) (lo hi : ℚ) (J terms : ℕ)
    (m : CompiledModel) (hc : ownCompile d p e lo hi J terms=some m) :
    let x := cqDiv (cqSub p d.mid) d.half
    let γ := cqDiv e d.half
    (cqSq d.half ≠ 0 ∧ x.2=0 ∧ (γ.2=0 ∨ (lo=0 ∧ hi=0)) ∧ lo ≤ hi ∧
      -1 ≤ x.1+γ.1*lo ∧ x.1+γ.1*lo ≤ 1 ∧
      -1 ≤ x.1+γ.1*hi ∧ x.1+γ.1*hi ≤ 1) ∧
      m.coeff=(List.range (J+1)).map (ownScalarCoeff d x γ terms) ∧
      m.error=seRat ((List.range (d.ownPolyQ.natDegree+1)).map (fun j : ℕ =>
        if J < j then |(qShiftCoeff d.ownPolyQ x γ j).1| *(max |lo| |hi|)^j else 0)).sum := by
  dsimp only [ownCompile] at hc
  split_ifs at hc with hg
  have hm := Option.some.inj hc
  cases hm
  exact ⟨hg,rfl,rfl⟩

theorem ownCompile_sound (d : QSegment) (p e : CQ) (lo hi : ℚ) (J terms : ℕ)
    (m : CompiledModel)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hc : ownCompile d p e lo hi J terms=some m) :
    ModelsOn (CellExpr.segment d p e).value (m.coeff.map ScalarExpr.value) lo hi m.error.value := by
  by_cases hsingle : lo=0 ∧ hi=0
  · obtain ⟨rfl,rfl⟩ := hsingle
    simpa only [Rat.cast_zero] using ownCompile_singleton_sound d p e J terms m hpos hc
  let x := cqDiv (cqSub p d.mid) d.half
  let γ := cqDiv e d.half
  rcases ownCompile_shape d p e lo hi J terms m hc with ⟨hg,hcoeff,herror⟩
  have hx2 : x.2=0 := hg.2.1
  have hγ2 : γ.2=0 := hg.2.2.1.resolve_right hsingle
  have hhalf : cqReal d.half ≠ 0 := by
    intro hz
    have he : (cqSq d.half:ℝ)=0 := by rw [cqSq_eq_norm_sq,hz,norm_zero]; norm_num
    exact hg.1 (by exact_mod_cast he)
  let pr : ℝ[X] := (d.ownPolyQ.map (Rat.castHom ℝ)).comp (C (x.1:ℝ)+C (γ.1:ℝ)*X)
  have hdeg : pr.natDegree ≤ d.ownPolyQ.natDegree := affine_natDegree_le _ _ _
  have hcv (j : ℕ) : ((qShiftCoeff d.ownPolyQ x γ j).1:ℝ)=pr.coeff j :=
    qShiftCoeff_real_spec _ x γ hx2 hγ2 j
  have herr : m.error.value = ∑ j ∈ Finset.range (d.ownPolyQ.natDegree+1),
      if J < j then |pr.coeff j| *(max |(lo:ℝ)| |(hi:ℝ)|)^j else 0 := by
    rw [herror,seRat_value,list_sum_map_range]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    change (((if J < j then |(qShiftCoeff d.ownPolyQ x γ j).1| *(max |lo| |hi|)^j else 0):ℚ):ℝ)=_
    by_cases hJ : J < j
    · simp only [if_pos hJ,Rat.cast_mul,Rat.cast_abs,Rat.cast_pow,Rat.cast_max,hcv]
    · simp only [if_neg hJ,Rat.cast_zero]
  have hcenter (u : ℝ) : cqReal d.mid+cqReal d.half*(((x.1:ℝ)+(γ.1:ℝ)*u:ℝ):ℂ) =
      cqReal p+cqReal e*(u:ℂ) := by
    have hxR : cqReal x=((x.1:ℝ):ℂ) := by simp [cqReal,hx2]
    have hγR : cqReal γ=((γ.1:ℝ):ℂ) := by simp [cqReal,hγ2]
    have hxq : cqReal x=(cqReal p-cqReal d.mid)/cqReal d.half := by
      dsimp only [x]; rw [cqReal_div,cqReal_sub]
    have hγq : cqReal γ=cqReal e/cqReal d.half := by dsimp only [γ]; rw [cqReal_div]
    simp only [Complex.ofReal_add,Complex.ofReal_mul]
    rw [← hxR,← hγR,hxq,hγq]
    field_simp [hhalf] <;> ring
  refine ⟨by exact_mod_cast hg.2.2.2.1,?_,?_⟩
  · rw [herr]
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> positivity
  · intro u hu
    have hlo : -1 ≤ (x.1:ℝ)+(γ.1:ℝ)*(lo:ℝ) ∧ (x.1:ℝ)+(γ.1:ℝ)*(lo:ℝ) ≤ 1 := by
      exact_mod_cast (show -1 ≤ x.1+γ.1*lo ∧ x.1+γ.1*lo ≤ 1 from ⟨hg.2.2.2.2.1,hg.2.2.2.2.2.1⟩)
    have hhi : -1 ≤ (x.1:ℝ)+(γ.1:ℝ)*(hi:ℝ) ∧ (x.1:ℝ)+(γ.1:ℝ)*(hi:ℝ) ≤ 1 := by
      exact_mod_cast (show -1 ≤ x.1+γ.1*hi ∧ x.1+γ.1*hi ≤ 1 from ⟨hg.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2⟩)
    have hp := d.own_point_value hhalf hpos _ (affine_interval_unit _ _ _ _ hlo hhi u hu)
    rw [hcenter u] at hp
    have heval : (d.ownPolyQ.map (Rat.castHom ℝ)).eval ((x.1:ℝ)+(γ.1:ℝ)*u)=pr.eval u := by
      simp [pr,Polynomial.eval_comp]
    rw [heval] at hp
    change |P d.measure (cqReal p+cqReal e*(u:ℂ))-evalModel (m.coeff.map ScalarExpr.value) u| ≤ _
    rw [hp,hcoeff,ownScalarCoeff_model,herr]
    have hs : (∑ j ∈ Finset.range (J+1), ((qShiftCoeff d.ownPolyQ x γ j).1:ℝ)*u^j) =
        ∑ j ∈ Finset.range (J+1), pr.coeff j*u^j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcv]
    rw [hs,add_sub_add_right_eq_sub]
    exact polynomial_truncation_bound_range pr J _ hdeg _ _ u hu

#print axioms affine_interval_unit
#print axioms ownCompile_shape
#print axioms ownCompile_sound

#print axioms affine_natDegree_le
#print axioms ownScalarCoeff_model

#print axioms polynomial_truncation_bound_range
#print axioms real_affine_map
#print axioms qShiftCoeff_real_spec
end
end CatalanCore.Li2.DecayCert
