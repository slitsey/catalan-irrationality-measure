module
public import CatalanCore.Li2.DecayCert.Compile.Defs
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section
theorem coeffEnclosed_sound (S a e : ℤ) (hS : 0 < S) (B : QBox) (x : ℝ)
    (hB : x ∈ Icc (B.1:ℝ) (B.2:ℝ)) (hc : coeffEnclosed S a e B=true) :
    0 ≤ e ∧ |dec S a-x| ≤ (e:ℝ)/(S:ℝ) := by
  have hh : 0 ≤ e ∧ ((a-e:ℤ):ℚ)/(S:ℚ) ≤ B.1 ∧ B.2 ≤ ((a+e:ℤ):ℚ)/(S:ℚ) :=
    of_decide_eq_true hc
  have hl : ((a-e:ℤ):ℝ)/(S:ℝ) ≤ (B.1:ℝ) := by exact_mod_cast hh.2.1
  have hu : (B.2:ℝ) ≤ ((a+e:ℤ):ℝ)/(S:ℝ) := by exact_mod_cast hh.2.2
  simp only [Int.cast_sub,Int.cast_add,sub_div,add_div] at hl hu
  refine ⟨hh.1,abs_le.mpr ⟨?_,?_⟩⟩ <;> dsimp [dec] <;> linarith [hB.1,hB.2]

theorem coefficientCheck_sound (S : ℤ) (m : CompiledModel) (w : CellWitness)
    (hc : coefficientCheck S m w=true) :
    0 < S ∧ m.coeff.length=w.coeff.length ∧ w.error.length=w.coeff.length ∧
      ∀ j < m.coeff.length, 0 ≤ getI w.error j ∧
        |dec S (getI w.coeff j)-(seGet m.coeff j).value| ≤
          (getI w.error j:ℝ)/(S:ℝ) := by
  simp only [coefficientCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  rcases hc with ⟨⟨hS,hlen,herr⟩,hall⟩
  refine ⟨hS,hlen,herr,?_⟩
  intro j hj
  have hh := List.all_eq_true.mp hall j (List.mem_range.mpr hj)
  cases hB : (seGet m.coeff j).check with
  | none => simp only [hB] at hh; contradiction
  | some B =>
    simp only [hB] at hh
    exact coeffEnclosed_sound S _ _ hS B _ (scalarCheck_sound _ B hB) hh

theorem cqReal_cqSum (xs : List CQ) : cqReal (cqSum xs)=(xs.map cqReal).sum := by
  have hh (xs : List CQ) (a : CQ) : cqReal (xs.foldl cqAdd a)=cqReal a+(xs.map cqReal).sum := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih => simp only [List.foldl_cons,ih,cqReal_add,List.map_cons,List.sum_cons]; ring
  simpa only [cqSum,cqReal,zero_add,zero_mul,Rat.cast_zero,add_zero] using hh xs (0,0)

theorem list_sum_map_range {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n : ℕ) :
    ((List.range n).map f).sum=∑ j ∈ Finset.range n,f j := by
  simpa only [List.toFinset_range] using (List.sum_toFinset f (List.nodup_range (n:=n))).symm

theorem polynomial_affine_coeff (p : ℚ[X]) (ζ γ : ℂ) (j : ℕ) :
    ((p.map (Rat.castHom ℂ)).comp (C ζ+C γ*X)).coeff j=
      ∑ k ∈ Finset.range (p.natDegree+1),
        (p.coeff k:ℂ)*(k.choose j:ℂ)*ζ^(k-j)*γ^j := by
  have he : p.map (Rat.castHom ℂ)=∑ k ∈ Finset.range (p.natDegree+1),C (p.coeff k:ℂ)*X^k := by
    conv_lhs => rw [p.as_sum_range]
    simp only [Polynomial.map_sum,Polynomial.map_monomial,Polynomial.C_mul_X_pow_eq_monomial,Rat.coe_castHom]
  have hc : (p.map (Rat.castHom ℂ)).comp (C ζ+C γ*X)=
      ((p.map (Rat.castHom ℂ)).comp (X+C ζ)).comp (C γ*X) := by
    rw [Polynomial.comp_assoc]
    congr 1
    simp [add_comm]
  rw [hc,Polynomial.comp_C_mul_X_coeff,he]
  simp only [Polynomial.sum_comp,Polynomial.C_mul_comp,Polynomial.C_comp,
    Polynomial.X_pow_comp,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem qShiftCoeff_spec (p : ℚ[X]) (ζ γ : CQ) (j : ℕ) :
    cqReal (qShiftCoeff p ζ γ j)=
      ((p.map (Rat.castHom ℂ)).comp (C (cqReal ζ)+C (cqReal γ)*X)).coeff j := by
  rw [qShiftCoeff,cqReal_cqSum,List.map_map,list_sum_map_range,polynomial_affine_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hj : j ≤ k
  · simp only [Function.comp_def,if_pos hj,cqReal_scale,cqReal_mul,cqReal_pow]
    push_cast
    ring
  · simp [hj,Nat.choose_eq_zero_of_lt (by omega : k < j),cqReal]

theorem remainderCheck_sound (S : ℤ) (rt : ℚ) (m : CompiledModel) (w : CellWitness)
    (hc : remainderCheck S rt m w=true) :
    0 ≤ (w.remainder:ℝ) ∧ 0 ≤ m.error.value ∧
      m.error.value+(∑ j ∈ Finset.range w.error.length,
        (getI w.error j:ℝ)/(S:ℝ)*(rt:ℝ)^j) ≤ (w.remainder:ℝ) := by
  cases hB : m.error.check with
  | none => simp [remainderCheck,hB] at hc
  | some B =>
    simp only [remainderCheck,hB] at hc
    have hh := of_decide_eq_true hc
    have hs := scalarCheck_sound m.error B hB
    have hBpos : (0:ℝ) ≤ (B.1:ℝ) := by exact_mod_cast hh.1
    have hwpos : (0:ℝ) ≤ (w.remainder:ℝ) := by exact_mod_cast hh.2.1
    have hsum : ((B.2+((List.range w.error.length).map (fun j : ℕ =>
        (getI w.error j:ℚ)/(S:ℚ)*rt^j)).sum:ℚ):ℝ) ≤ (w.remainder:ℝ) := Rat.cast_le.mpr hh.2.2
    rw [list_sum_map_range,Rat.cast_add,Rat.cast_sum] at hsum
    have hcast : (∑ j ∈ Finset.range w.error.length,
        (((getI w.error j:ℚ)/(S:ℚ)*rt^j:ℚ):ℝ))=
        ∑ j ∈ Finset.range w.error.length,(getI w.error j:ℝ)/(S:ℝ)*(rt:ℝ)^j := by
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      rfl
    rw [hcast] at hsum
    exact ⟨hwpos,hBpos.trans hs.1,by linarith [hs.2]⟩

theorem evalModel_map_scalar (a : List SE) (u : ℝ) :
    evalModel (a.map ScalarExpr.value) u=∑ j ∈ Finset.range a.length,(seGet a j).value*u^j := by
  unfold evalModel
  simp only [List.length_map]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < a.length := Finset.mem_range.mp hj
  simp [List.getElem!_eq_getElem?_getD,seGet,List.getElem?_eq_getElem hj']

theorem gridCoeffs_value (S : ℤ) (w : CellWitness) (j : ℕ) :
    (coeffQ (gridCoeffs S w) j:ℝ)=dec S (getI w.coeff j) := by
  cases hh : w.coeff[j]? with
  | none => simp [gridCoeffs,coeffQ,getI,hh,dec]
  | some a => simp [gridCoeffs,coeffQ,getI,hh,dec]

theorem round_coeff_error (S : ℤ) (m : CompiledModel) (w : CellWitness)
    (hc : coefficientCheck S m w=true) (rt u : ℝ) (hu : |u| ≤ rt) :
    |evalModel (m.coeff.map ScalarExpr.value) u-
      evalModel ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) u| ≤
      ∑ j ∈ Finset.range m.coeff.length,(getI w.error j:ℝ)/(S:ℝ)*rt^j := by
  have hh := coefficientCheck_sound S m w hc
  have hS : (0:ℝ)<(S:ℝ) := by exact_mod_cast hh.1
  have hlen : (gridCoeffs S w).length=m.coeff.length := by simp [gridCoeffs,hh.2.1]
  rw [evalModel_map_scalar,evalModel_map_rat,hlen,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [gridCoeffs_value,← sub_mul,abs_mul,abs_sub_comm,abs_pow]
  have hcj := hh.2.2.2 j (Finset.mem_range.mp hj)
  have he : (0:ℝ) ≤ (getI w.error j:ℝ) := by exact_mod_cast hcj.1
  exact mul_le_mul hcj.2 (pow_le_pow_left₀ (abs_nonneg u) hu j)
    (pow_nonneg (abs_nonneg u) j) (div_nonneg he hS.le)

theorem roundModel_sound (S : ℤ) (lo hi : ℚ) (m : CompiledModel) (w : CellWitness)
    (f : ℝ → ℝ) (hm : ModelsOn f (m.coeff.map ScalarExpr.value) lo hi m.error.value)
    (hc : coefficientCheck S m w=true)
    (hr : remainderCheck S (max |lo| |hi|) m w=true) :
    ModelsOn f ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) lo hi w.remainder := by
  have hrem := remainderCheck_sound S (max |lo| |hi|) m w hr
  have hco := coefficientCheck_sound S m w hc
  have hlen : w.error.length=m.coeff.length := hco.2.2.1.trans hco.2.1.symm
  rw [hlen] at hrem
  refine ⟨hm.1,hrem.1,?_⟩
  intro u hu
  have hrt : |u| ≤ ((max |lo| |hi|:ℚ):ℝ) := by
    rw [Rat.cast_max,Rat.cast_abs,Rat.cast_abs]
    exact abs_le.mpr
      ⟨by have := le_max_left |(lo:ℝ)| |(hi:ℝ)|; have := neg_abs_le (lo:ℝ); linarith [hu.1],
        by have := le_max_right |(lo:ℝ)| |(hi:ℝ)|; have := le_abs_self (hi:ℝ); linarith [hu.2]⟩
  have hround := round_coeff_error S m w hc _ u hrt
  have hmodel := hm.2.2 u hu
  have htri := norm_add_le (f u-evalModel (m.coeff.map ScalarExpr.value) u)
    (evalModel (m.coeff.map ScalarExpr.value) u-
      evalModel ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) u)
  have he : f u-evalModel (m.coeff.map ScalarExpr.value) u+
      (evalModel (m.coeff.map ScalarExpr.value) u-
        evalModel ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) u)=
      f u-evalModel ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) u := by ring
  simp only [Real.norm_eq_abs] at htri
  rw [he] at htri
  linarith [hrem.2.2]

theorem seGet_value_of_ge (a : List SE) (j : ℕ) (hj : a.length ≤ j) :
    (seGet a j).value=0 := by simp [seGet,List.getElem?_eq_none hj,ScalarExpr.value]

theorem seGet_map_scale_value (a : List SE) (c : ℚ) (j : ℕ) :
    (seGet (a.map (seScale c)) j).value=(c:ℝ)*(seGet a j).value := by
  cases hh : a[j]? <;> simp [seGet,hh,seScale_value,ScalarExpr.value]

theorem evalModel_scale_scalar (a : List SE) (c : ℚ) (u : ℝ) :
    evalModel ((a.map (seScale c)).map ScalarExpr.value) u=
      (c:ℝ)*evalModel (a.map ScalarExpr.value) u := by
  rw [evalModel_map_scalar,evalModel_map_scalar,List.length_map,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [seGet_map_scale_value]
  ring

theorem evalModel_range (f : ℕ → ℝ) (n : ℕ) (u : ℝ) :
    evalModel ((List.range n).map f) u=∑ j ∈ Finset.range n,f j*u^j := by
  unfold evalModel
  simp only [List.length_map,List.length_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp [List.getElem!_eq_getElem?_getD,List.getElem?_range (Finset.mem_range.mp hj)]

theorem evalModel_extend_scalar (a : List SE) (u : ℝ) (n : ℕ) (hn : a.length ≤ n) :
    (∑ j ∈ Finset.range n,(seGet a j).value*u^j)=evalModel (a.map ScalarExpr.value) u := by
  rw [evalModel_map_scalar]
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro j hj hnot
  have hj' : a.length ≤ j := by simpa only [Finset.mem_range,not_lt] using hnot
  rw [seGet_value_of_ge a j hj',zero_mul]

theorem evalModel_combine_scalar (a b : List SE) (u : ℝ) :
    evalModel ((combineCoeffs a b).map ScalarExpr.value) u=
      evalModel (a.map ScalarExpr.value) u+evalModel (b.map ScalarExpr.value) u := by
  rw [combineCoeffs,List.map_map,evalModel_range]
  simp only [Function.comp_def,seAdd_value,add_mul,Finset.sum_add_distrib]
  rw [evalModel_extend_scalar a u _ (le_max_left _ _),
    evalModel_extend_scalar b u _ (le_max_right _ _)]

theorem ModelsOn.scale_scalar {f : ℝ → ℝ} {a : List SE} {l r err : ℝ}
    (hm : ModelsOn f (a.map ScalarExpr.value) l r err) (c : ℚ) :
    ModelsOn (fun u => (c:ℝ)*f u) ((a.map (seScale c)).map ScalarExpr.value) l r (|(c:ℝ)| *err) := by
  refine ⟨hm.1,mul_nonneg (abs_nonneg _) hm.2.1,?_⟩
  intro u hu
  rw [evalModel_scale_scalar,← mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left (hm.2.2 u hu) (abs_nonneg _)

theorem ModelsOn.add_scalar {f g : ℝ → ℝ} {a b : List SE} {l r e₁ e₂ : ℝ}
    (hf : ModelsOn f (a.map ScalarExpr.value) l r e₁)
    (hg : ModelsOn g (b.map ScalarExpr.value) l r e₂) :
    ModelsOn (fun u => f u+g u) ((combineCoeffs a b).map ScalarExpr.value) l r (e₁+e₂) := by
  refine ⟨hf.1,add_nonneg hf.2.1 hg.2.1,?_⟩
  intro u hu
  rw [evalModel_combine_scalar]
  have ht := norm_add_le (f u-evalModel (a.map ScalarExpr.value) u)
    (g u-evalModel (b.map ScalarExpr.value) u)
  simp only [Real.norm_eq_abs] at ht
  have he : f u-evalModel (a.map ScalarExpr.value) u+(g u-evalModel (b.map ScalarExpr.value) u)=
      f u+g u-(evalModel (a.map ScalarExpr.value) u+evalModel (b.map ScalarExpr.value) u) := by ring
  rw [he] at ht
  linarith [hf.2.2 u hu,hg.2.2 u hu]

#print axioms coeffEnclosed_sound
#print axioms coefficientCheck_sound
#print axioms cqReal_cqSum
#print axioms list_sum_map_range
#print axioms polynomial_affine_coeff
#print axioms qShiftCoeff_spec
#print axioms remainderCheck_sound
#print axioms evalModel_map_scalar
#print axioms gridCoeffs_value
#print axioms round_coeff_error
#print axioms roundModel_sound
#print axioms seGet_value_of_ge
#print axioms seGet_map_scale_value
#print axioms evalModel_scale_scalar
#print axioms evalModel_range
#print axioms evalModel_extend_scalar
#print axioms evalModel_combine_scalar
#print axioms ModelsOn.scale_scalar
#print axioms ModelsOn.add_scalar
end
end CatalanCore.Li2.DecayCert
