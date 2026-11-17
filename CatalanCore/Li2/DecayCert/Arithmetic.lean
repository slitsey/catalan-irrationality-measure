module

public import Mathlib.Data.Int.DivMod
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
set_option Elab.async false

namespace CatalanCore.Li2.DecayCert

def fm (S a b : ℤ) : ℤ := (a*b)/S
def fd (S a b : ℤ) : ℤ := (S*a)/b
noncomputable def dec (S a : ℤ) : ℝ := (a:ℝ)/(S:ℝ)

/-- Euclidean division has error below one, including negative divisors. -/
theorem ediv_real_error (a b : ℤ) (hb : b ≠ 0) :
    |((a/b:ℤ):ℝ)-(a:ℝ)/(b:ℝ)| < 1 := by
  have hbR : (b:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hr : (0:ℝ) ≤ ((a%b:ℤ):ℝ) := by exact_mod_cast Int.emod_nonneg a hb
  have hrlt : ((a%b:ℤ):ℝ) < |(b:ℝ)| := by exact_mod_cast Int.emod_lt a hb
  have hdecomp : ((a%b:ℤ):ℝ)+((a/b:ℤ):ℝ)*(b:ℝ)=(a:ℝ) := by
    exact_mod_cast Int.emod_add_ediv_mul a b
  have heq : ((a/b:ℤ):ℝ)-(a:ℝ)/(b:ℝ) = -((a%b:ℤ):ℝ)/(b:ℝ) := by
    apply (eq_div_iff hbR).2
    rw [sub_mul, div_mul_cancel₀ _ hbR]
    linarith
  rw [heq, abs_div, abs_neg, abs_of_nonneg hr]
  exact (div_lt_one (abs_pos.mpr hbR)).2 hrlt

theorem ediv_grid_error (S a b : ℤ) (hS : 0 < S) (hb : b ≠ 0) :
    |dec S (a/b)-((a:ℝ)/(b:ℝ))/(S:ℝ)| < 1/(S:ℝ) := by
  have hSR : (0:ℝ) < (S:ℝ) := by exact_mod_cast hS
  unfold dec
  rw [← sub_div, abs_div, abs_of_pos hSR]
  exact div_lt_div_of_pos_right (ediv_real_error a b hb) hSR

theorem fm_spec (S a b : ℤ) (hS : 0 < S) :
    |dec S (fm S a b)-dec S a*dec S b| < 1/(S:ℝ) := by
  have hSR : (S:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hS.ne'
  have heq : dec S (fm S a b)-dec S a*dec S b =
      dec S ((a*b)/S)-(((a*b:ℤ):ℝ)/(S:ℝ))/(S:ℝ) := by
    unfold dec fm
    push_cast
    field_simp [hSR]
    <;> ring
  rw [heq]
  exact ediv_grid_error S (a*b) S hS hS.ne'

theorem fd_spec (S a b : ℤ) (hS : 0 < S) (hb : b ≠ 0) :
    |dec S (fd S a b)-dec S a/dec S b| < 1/(S:ℝ) := by
  have hSR : (S:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hS.ne'
  have hbR : (b:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have heq : dec S (fd S a b)-dec S a/dec S b =
      dec S ((S*a)/b)-(((S*a:ℤ):ℝ)/(b:ℝ))/(S:ℝ) := by
    unfold dec fd
    push_cast
    field_simp [hSR, hbR]
    <;> ring
  rw [heq]
  exact ediv_grid_error S (S*a) b hS hb

open Polynomial

theorem taylorShift_spec (p : Polynomial ℂ) (c e u : ℂ) :
    (p.comp (Polynomial.C c+Polynomial.C e*Polynomial.X)).eval u=p.eval (c+e*u) := by
  simp

abbrev CI := ℤ×ℤ

def ciGet (xs : List CI) (j : ℕ) : CI := xs[j]?.getD (0,0)
def ciAdd (a b : CI) : CI := (a.1+b.1,a.2+b.2)
def ciMulF (S : ℤ) (a b : CI) : CI :=
  (fm S a.1 b.1-fm S a.2 b.2,fm S a.1 b.2+fm S a.2 b.1)
def ciMag (S : ℤ) (a : CI) : ℚ := (|a.1|+|a.2|:ℤ)/(S:ℚ)
noncomputable def ciValue (S : ℤ) (a : CI) : ℂ :=
  (dec S a.1:ℂ)+(dec S a.2:ℂ)*Complex.I

theorem dec_add (S a b : ℤ) : dec S (a+b)=dec S a+dec S b := by
  simp [dec,add_div]
theorem dec_sub (S a b : ℤ) : dec S (a-b)=dec S a-dec S b := by
  simp [dec,sub_div]
theorem ciValue_add (S : ℤ) (a b : CI) :
    ciValue S (ciAdd a b)=ciValue S a+ciValue S b := by
  simp [ciValue,ciAdd,dec_add]; ring

theorem norm_re_im_le (x y : ℝ) : ‖(x:ℂ)+(y:ℂ)*Complex.I‖ ≤ |x|+|y| := by
  calc
    _ ≤ ‖(x:ℂ)‖+‖(y:ℂ)*Complex.I‖ := norm_add_le _ _
    _ = _ := by simp

theorem ciValue_norm_le (S : ℤ) (a : CI) (hS : 0 < S) :
    ‖ciValue S a‖ ≤ (ciMag S a:ℝ) := by
  have hs : (0:ℝ)<(S:ℝ) := by exact_mod_cast hS
  calc
    _ ≤ |dec S a.1|+|dec S a.2| := norm_re_im_le _ _
    _ = _ := by simp [dec,ciMag,abs_div,abs_of_pos hs,add_div]

theorem ciMulF_spec (S : ℤ) (a b : CI) (hS : 0 < S) :
    ‖ciValue S (ciMulF S a b)-ciValue S a*ciValue S b‖ ≤ 4/(S:ℝ) := by
  let e₁ := dec S (fm S a.1 b.1)-dec S a.1*dec S b.1
  let e₂ := dec S (fm S a.2 b.2)-dec S a.2*dec S b.2
  let e₃ := dec S (fm S a.1 b.2)-dec S a.1*dec S b.2
  let e₄ := dec S (fm S a.2 b.1)-dec S a.2*dec S b.1
  have h₁ : |e₁|<1/(S:ℝ) := fm_spec S a.1 b.1 hS
  have h₂ : |e₂|<1/(S:ℝ) := fm_spec S a.2 b.2 hS
  have h₃ : |e₃|<1/(S:ℝ) := fm_spec S a.1 b.2 hS
  have h₄ : |e₄|<1/(S:ℝ) := fm_spec S a.2 b.1 hS
  have heq : ciValue S (ciMulF S a b)-ciValue S a*ciValue S b =
      ((e₁-e₂:ℝ):ℂ)+((e₃+e₄:ℝ):ℂ)*Complex.I := by
    simp only [ciValue,ciMulF,dec_add,dec_sub,e₁,e₂,e₃,e₄]
    push_cast
    linear_combination -dec S a.2*dec S b.2*Complex.I_sq
  rw [heq]
  calc
    _ ≤ |e₁-e₂|+|e₃+e₄| := norm_re_im_le _ _
    _ ≤ (|e₁|+|e₂|)+(|e₃|+|e₄|) := add_le_add (abs_sub _ _) (abs_add_le _ _)
    _ ≤ 4/(S:ℝ) := by
      simp only [div_eq_mul_inv,one_mul] at h₁ h₂ h₃ h₄ ⊢
      linarith

theorem fm_error_propagation (S C v : ℤ) (x err : ℝ) (hS : 0 < S)
    (hv : |dec S v-x| ≤ err) :
    |dec S (fm S C v)-dec S C*x| ≤ |dec S C| *err+1/(S:ℝ) := by
  have hf := (fm_spec S C v hS).le
  have heq : dec S (fm S C v)-dec S C*x =
      (dec S (fm S C v)-dec S C*dec S v)+dec S C*(dec S v-x) := by ring
  rw [heq]
  calc
    _ ≤ |dec S (fm S C v)-dec S C*dec S v|+|dec S C*(dec S v-x)| := abs_add_le _ _
    _ ≤ 1/(S:ℝ)+|dec S C| *err := by
      rw [abs_mul]
      exact add_le_add hf (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
    _ = _ := by ring

theorem ciMulF_error_propagation (S : ℤ) (C v : CI) (x : ℂ) (err : ℝ) (hS : 0 < S)
    (hv : ‖ciValue S v-x‖ ≤ err) :
    ‖ciValue S (ciMulF S C v)-ciValue S C*x‖ ≤ (ciMag S C:ℝ)*err+4/(S:ℝ) := by
  have hf := ciMulF_spec S C v hS
  have he : 0 ≤ err := (norm_nonneg _).trans hv
  have heq : ciValue S (ciMulF S C v)-ciValue S C*x =
      (ciValue S (ciMulF S C v)-ciValue S C*ciValue S v)+ciValue S C*(ciValue S v-x) := by ring
  rw [heq]
  calc
    _ ≤ ‖ciValue S (ciMulF S C v)-ciValue S C*ciValue S v‖+‖ciValue S C*(ciValue S v-x)‖ := norm_add_le _ _
    _ ≤ 4/(S:ℝ)+(ciMag S C:ℝ)*err := by
      rw [norm_mul]
      exact add_le_add hf (mul_le_mul (ciValue_norm_le S C hS) hv (norm_nonneg _) (by
        exact (norm_nonneg _).trans (ciValue_norm_le S C hS)))
    _ = _ := by ring

def getI (v : List ℤ) (j : ℕ) : ℤ := v[j]?.getD 0
def getQ (v : List ℚ) (j : ℕ) : ℚ := v[j]?.getD 0
def hornerGridStep (S C E a : ℤ) (v : List ℤ) : List ℤ :=
  (List.range v.length).map (fun j =>
    fm S C (getI v j)+(if j=0 then a else fm S E (getI v (j-1))))
def hornerErrorStep (S C E : ℤ) (err : List ℚ) : List ℚ :=
  (List.range err.length).map (fun j =>
    |(C:ℚ)/(S:ℚ)| *getQ err j+1/(S:ℚ)+
      if j=0 then 0 else |(E:ℚ)/(S:ℚ)| *getQ err (j-1)+1/(S:ℚ))
structure ShiftStep where
  value : List ℤ
  error : List ℚ

def shiftSteps (S C E : ℤ) : List ℤ → ShiftStep → ShiftStep
  | [],w => w
  | a::rest,w => shiftSteps S C E rest
      ⟨hornerGridStep S C E a w.value,hornerErrorStep S C E w.error⟩
def shiftComputed (S C E : ℤ) (p : List ℤ) : ShiftStep :=
  shiftSteps S C E p.reverse
    ⟨List.replicate p.length 0,List.replicate p.length 0⟩
def shiftCheck (S C E : ℤ) (p out : List ℤ) (err : List ℚ) : Bool :=
  decide (0 < S ∧ out=(shiftComputed S C E p).value ∧ err=(shiftComputed S C E p).error)
noncomputable def gridPoly (S : ℤ) (p : List ℤ) : ℝ[X] :=
  ∑ j ∈ Finset.range p.length, Polynomial.C (dec S (getI p j))*Polynomial.X^j

theorem getI_hornerGridStep (S C E a : ℤ) (v : List ℤ) (j : ℕ) (hj : j<v.length) :
    getI (hornerGridStep S C E a v) j =
      fm S C (getI v j)+(if j=0 then a else fm S E (getI v (j-1))) := by
  simp [getI,hornerGridStep,List.getElem?_map,List.getElem?_range,hj]

theorem getQ_hornerErrorStep (S C E : ℤ) (v : List ℚ) (j : ℕ) (hj : j<v.length) :
    getQ (hornerErrorStep S C E v) j =
      |(C:ℚ)/(S:ℚ)| *getQ v j+1/(S:ℚ)+
        (if j=0 then 0 else |(E:ℚ)/(S:ℚ)| *getQ v (j-1)+1/(S:ℚ)) := by
  simp [getQ,hornerErrorStep,List.getElem?_map,List.getElem?_range,hj]

noncomputable def hornerPoly (S C E a : ℤ) (q : ℝ[X]) : ℝ[X] :=
  Polynomial.C (dec S a)+(Polynomial.C (dec S C)+Polynomial.C (dec S E)*Polynomial.X)*q

theorem hornerPoly_coeff (S C E a : ℤ) (q : ℝ[X]) (j : ℕ) :
    (hornerPoly S C E a q).coeff j =
      dec S C*q.coeff j+(if j=0 then dec S a else dec S E*q.coeff (j-1)) := by
  cases j with
  | zero => simp [hornerPoly]; ring
  | succ j => simp [hornerPoly,add_mul,mul_assoc,Polynomial.coeff_X_mul]

def ShiftModels (S : ℤ) (n : ℕ) (w : ShiftStep) (q : ℝ[X]) : Prop :=
  w.value.length=n ∧ w.error.length=n ∧ ∀ j < n,
    |dec S (getI w.value j)-q.coeff j| ≤ (getQ w.error j:ℝ)

theorem hornerStep_models (S C E a : ℤ) (hS : 0 < S) (n : ℕ)
    (w : ShiftStep) (q : ℝ[X]) (hw : ShiftModels S n w q) :
    ShiftModels S n ⟨hornerGridStep S C E a w.value,hornerErrorStep S C E w.error⟩
      (hornerPoly S C E a q) := by
  rcases hw with ⟨hlv,hle,hw⟩
  refine ⟨by simpa [hornerGridStep] using hlv,by simpa [hornerErrorStep] using hle,?_⟩
  intro j hj
  change |dec S (getI (hornerGridStep S C E a w.value) j)-
    (hornerPoly S C E a q).coeff j| ≤ (getQ (hornerErrorStep S C E w.error) j:ℝ)
  rw [getI_hornerGridStep S C E a w.value j (by omega),
    getQ_hornerErrorStep S C E w.error j (by omega),hornerPoly_coeff]
  have h₁ := fm_error_propagation S C (getI w.value j) (q.coeff j) (getQ w.error j) hS (hw j hj)
  by_cases hj0 : j=0
  · subst j
    simp only [ite_true,add_zero]
    rw [dec_add]
    have heq : dec S (fm S C (getI w.value 0))+dec S a-(dec S C*q.coeff 0+dec S a)=
        dec S (fm S C (getI w.value 0))-dec S C*q.coeff 0 := by ring
    rw [heq]
    simpa [dec] using h₁
  · have hjprev : j-1<n := by omega
    have h₂ := fm_error_propagation S E (getI w.value (j-1)) (q.coeff (j-1))
      (getQ w.error (j-1)) hS (hw (j-1) hjprev)
    simp only [hj0,ite_false]
    rw [dec_add]
    have heq : dec S (fm S C (getI w.value j))+dec S (fm S E (getI w.value (j-1)))-
        (dec S C*q.coeff j+dec S E*q.coeff (j-1)) =
        (dec S (fm S C (getI w.value j))-dec S C*q.coeff j)+
        (dec S (fm S E (getI w.value (j-1)))-dec S E*q.coeff (j-1)) := by ring
    rw [heq]
    have hb := (abs_add_le _ _).trans (add_le_add h₁ h₂)
    simpa [dec] using hb

noncomputable def hornerSteps (S C E : ℤ) : List ℤ → ℝ[X] → ℝ[X]
  | [],q => q
  | a::rest,q => hornerSteps S C E rest (hornerPoly S C E a q)

theorem shiftSteps_models (S C E : ℤ) (hS : 0 < S) (n : ℕ) (p : List ℤ)
    (w : ShiftStep) (q : ℝ[X]) (hw : ShiftModels S n w q) :
    ShiftModels S n (shiftSteps S C E p w) (hornerSteps S C E p q) := by
  induction p generalizing w q with
  | nil => exact hw
  | cons a p ih => exact ih _ _ (hornerStep_models S C E a hS n w q hw)

theorem hornerSteps_append (S C E : ℤ) (p t : List ℤ) (q : ℝ[X]) :
    hornerSteps S C E (p++t) q=hornerSteps S C E t (hornerSteps S C E p q) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih => exact ih _

theorem gridPoly_cons (S a : ℤ) (p : List ℤ) :
    gridPoly S (a::p)=Polynomial.C (dec S a)+Polynomial.X*gridPoly S p := by
  classical
  unfold gridPoly
  rw [List.length_cons,Finset.sum_range_succ']
  simp only [getI,List.getElem?_cons_zero,Option.getD_some,pow_zero,mul_one,
    List.getElem?_cons_succ]
  rw [Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_succ]
  ring

theorem hornerSteps_reverse (S C E : ℤ) (p : List ℤ) :
    hornerSteps S C E p.reverse 0=
      (gridPoly S p).comp (Polynomial.C (dec S C)+Polynomial.C (dec S E)*Polynomial.X) := by
  induction p with
  | nil => simp [hornerSteps,gridPoly]
  | cons a p ih =>
    rw [List.reverse_cons,hornerSteps_append]
    simp only [hornerSteps]
    rw [ih,gridPoly_cons]
    simp only [Polynomial.add_comp,Polynomial.C_comp,Polynomial.mul_comp,Polynomial.X_comp]
    rfl

theorem taylorShiftF_spec (S C E : ℤ) (p out : List ℤ) (err : List ℚ)
    (hc : shiftCheck S C E p out err=true) :
    out.length=p.length ∧ err.length=p.length ∧ ∀ j < p.length,
      |dec S (getI out j)-
        ((gridPoly S p).comp (Polynomial.C (dec S C)+Polynomial.C (dec S E)*Polynomial.X)).coeff j| ≤
        (getQ err j:ℝ) := by
  have hcheck : 0 < S ∧ out=(shiftComputed S C E p).value ∧
      err=(shiftComputed S C E p).error := of_decide_eq_true hc
  rcases hcheck with ⟨hS,rfl,rfl⟩
  have hinit : ShiftModels S p.length
      ⟨List.replicate p.length 0,List.replicate p.length 0⟩ 0 := by
    refine ⟨by simp,by simp,?_⟩
    intro j hj
    simp [getI,getQ,List.getElem?_replicate,hj,dec]
  have hh := shiftSteps_models S C E hS p.length p.reverse _ _ hinit
  rw [hornerSteps_reverse] at hh
  exact hh

structure CShiftStep where
  value : List CI
  error : List ℚ

def cHornerStep (S : ℤ) (C E a : CI) (w : CShiftStep) : CShiftStep :=
  ⟨(List.range w.value.length).map (fun j =>
      ciAdd (ciMulF S C (ciGet w.value j))
        (if j=0 then a else ciMulF S E (ciGet w.value (j-1)))),
    (List.range w.error.length).map (fun j =>
      ciMag S C*getQ w.error j+4/(S:ℚ)+
        (if j=0 then 0 else ciMag S E*getQ w.error (j-1)+4/(S:ℚ)))⟩
def cShiftSteps (S : ℤ) (C E : CI) : List CI → CShiftStep → CShiftStep
  | [],w => w
  | a::rest,w => cShiftSteps S C E rest (cHornerStep S C E a w)
def cShiftComputed (S : ℤ) (C E : CI) (p : List CI) : CShiftStep :=
  cShiftSteps S C E p.reverse
    ⟨List.replicate p.length (0,0),List.replicate p.length 0⟩
def cShiftCheck (S : ℤ) (C E : CI) (p out : List CI) (err : List ℚ) : Bool :=
  decide (0 < S ∧ out=(cShiftComputed S C E p).value ∧ err=(cShiftComputed S C E p).error)
noncomputable def cGridPoly (S : ℤ) (p : List CI) : ℂ[X] :=
  ∑ j ∈ Finset.range p.length, Polynomial.C (ciValue S (ciGet p j))*Polynomial.X^j
noncomputable def cHornerPoly (S : ℤ) (C E a : CI) (q : ℂ[X]) : ℂ[X] :=
  Polynomial.C (ciValue S a)+(Polynomial.C (ciValue S C)+Polynomial.C (ciValue S E)*Polynomial.X)*q

theorem cHornerPoly_coeff (S : ℤ) (C E a : CI) (q : ℂ[X]) (j : ℕ) :
    (cHornerPoly S C E a q).coeff j =
      ciValue S C*q.coeff j+(if j=0 then ciValue S a else ciValue S E*q.coeff (j-1)) := by
  cases j with
  | zero => simp [cHornerPoly]; ring
  | succ j => simp [cHornerPoly,add_mul,mul_assoc,Polynomial.coeff_X_mul]

def CShiftModels (S : ℤ) (n : ℕ) (w : CShiftStep) (q : ℂ[X]) : Prop :=
  w.value.length=n ∧ w.error.length=n ∧ ∀ j < n,
    ‖ciValue S (ciGet w.value j)-q.coeff j‖ ≤ (getQ w.error j:ℝ)

theorem cHornerStep_models (S : ℤ) (C E a : CI) (hS : 0 < S) (n : ℕ)
    (w : CShiftStep) (q : ℂ[X]) (hw : CShiftModels S n w q) :
    CShiftModels S n (cHornerStep S C E a w) (cHornerPoly S C E a q) := by
  rcases hw with ⟨hlv,hle,hw⟩
  refine ⟨by simpa [cHornerStep] using hlv,by simpa [cHornerStep] using hle,?_⟩
  intro j hj
  have hv : ciGet (cHornerStep S C E a w).value j =
      ciAdd (ciMulF S C (ciGet w.value j))
        (if j=0 then a else ciMulF S E (ciGet w.value (j-1))) := by
    simp [ciGet,cHornerStep,hlv,hj]
  have he : getQ (cHornerStep S C E a w).error j =
      ciMag S C*getQ w.error j+4/(S:ℚ)+
        (if j=0 then 0 else ciMag S E*getQ w.error (j-1)+4/(S:ℚ)) := by
    simp [getQ,cHornerStep,hle,hj]
  change ‖ciValue S (ciGet (cHornerStep S C E a w).value j)-
    (cHornerPoly S C E a q).coeff j‖ ≤ (getQ (cHornerStep S C E a w).error j:ℝ)
  rw [hv,he,cHornerPoly_coeff]
  have h₁ := ciMulF_error_propagation S C (ciGet w.value j) (q.coeff j) (getQ w.error j) hS (hw j hj)
  by_cases hj0 : j=0
  · subst j
    simp only [ite_true,add_zero]
    rw [ciValue_add]
    have heq : ciValue S (ciMulF S C (ciGet w.value 0))+ciValue S a-
        (ciValue S C*q.coeff 0+ciValue S a)=
        ciValue S (ciMulF S C (ciGet w.value 0))-ciValue S C*q.coeff 0 := by ring
    rw [heq]
    simpa using h₁
  · have hjprev : j-1<n := by omega
    have h₂ := ciMulF_error_propagation S E (ciGet w.value (j-1)) (q.coeff (j-1))
      (getQ w.error (j-1)) hS (hw (j-1) hjprev)
    simp only [hj0,ite_false]
    rw [ciValue_add]
    have heq : ciValue S (ciMulF S C (ciGet w.value j))+ciValue S (ciMulF S E (ciGet w.value (j-1)))-
        (ciValue S C*q.coeff j+ciValue S E*q.coeff (j-1)) =
        (ciValue S (ciMulF S C (ciGet w.value j))-ciValue S C*q.coeff j)+
        (ciValue S (ciMulF S E (ciGet w.value (j-1)))-ciValue S E*q.coeff (j-1)) := by ring
    rw [heq]
    have hb := (norm_add_le _ _).trans (add_le_add h₁ h₂)
    simpa using hb

noncomputable def cHornerSteps (S : ℤ) (C E : CI) : List CI → ℂ[X] → ℂ[X]
  | [],q => q
  | a::rest,q => cHornerSteps S C E rest (cHornerPoly S C E a q)

theorem cShiftSteps_models (S : ℤ) (C E : CI) (hS : 0 < S) (n : ℕ) (p : List CI)
    (w : CShiftStep) (q : ℂ[X]) (hw : CShiftModels S n w q) :
    CShiftModels S n (cShiftSteps S C E p w) (cHornerSteps S C E p q) := by
  induction p generalizing w q with
  | nil => exact hw
  | cons a p ih => exact ih _ _ (cHornerStep_models S C E a hS n w q hw)

theorem cHornerSteps_append (S : ℤ) (C E : CI) (p t : List CI) (q : ℂ[X]) :
    cHornerSteps S C E (p++t) q=cHornerSteps S C E t (cHornerSteps S C E p q) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih => exact ih _

theorem cGridPoly_cons (S : ℤ) (a : CI) (p : List CI) :
    cGridPoly S (a::p)=Polynomial.C (ciValue S a)+Polynomial.X*cGridPoly S p := by
  classical
  unfold cGridPoly
  rw [List.length_cons,Finset.sum_range_succ']
  simp only [ciGet,List.getElem?_cons_zero,Option.getD_some,pow_zero,mul_one,
    List.getElem?_cons_succ]
  rw [Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_succ]
  ring

theorem cHornerSteps_reverse (S : ℤ) (C E : CI) (p : List CI) :
    cHornerSteps S C E p.reverse 0=
      (cGridPoly S p).comp (Polynomial.C (ciValue S C)+Polynomial.C (ciValue S E)*Polynomial.X) := by
  induction p with
  | nil => simp [cHornerSteps,cGridPoly]
  | cons a p ih =>
    rw [List.reverse_cons,cHornerSteps_append]
    simp only [cHornerSteps]
    rw [ih,cGridPoly_cons]
    simp only [Polynomial.add_comp,Polynomial.C_comp,Polynomial.mul_comp,Polynomial.X_comp]
    rfl

theorem taylorShiftCF_spec (S : ℤ) (C E : CI) (p out : List CI) (err : List ℚ)
    (hc : cShiftCheck S C E p out err=true) :
    out.length=p.length ∧ err.length=p.length ∧ ∀ j < p.length,
      ‖ciValue S (ciGet out j)-
        ((cGridPoly S p).comp (Polynomial.C (ciValue S C)+Polynomial.C (ciValue S E)*Polynomial.X)).coeff j‖ ≤
        (getQ err j:ℝ) := by
  have hcheck : 0 < S ∧ out=(cShiftComputed S C E p).value ∧
      err=(cShiftComputed S C E p).error := of_decide_eq_true hc
  rcases hcheck with ⟨hS,rfl,rfl⟩
  have hinit : CShiftModels S p.length
      ⟨List.replicate p.length (0,0),List.replicate p.length 0⟩ 0 := by
    refine ⟨by simp,by simp,?_⟩
    intro j hj
    simp [ciGet,getQ,hj,ciValue,dec]
  have hh := cShiftSteps_models S C E hS p.length p.reverse _ _ hinit
  rw [cHornerSteps_reverse] at hh
  exact hh

#print axioms fm_spec
#print axioms fd_spec
#print axioms taylorShift_spec
#print axioms taylorShiftF_spec
#print axioms taylorShiftCF_spec
end CatalanCore.Li2.DecayCert
