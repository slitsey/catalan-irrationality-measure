module
public import CatalanCore.Li2.Family
public import CatalanCore.Li2.NV.Definitions
public import CatalanCore.Li2.NVMod.Moments
public import CatalanCore.Content.CrtBasis
public import CatalanCore.Lai.NVCore
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P045
public import CatalanCore.Li2.Port.Unified.Modular.Base.ParameterShift
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1000000
open Polynomial Matrix Finset
open scoped BigOperators
namespace CatalanCore.Li2.NV
open NVMod
noncomputable section
abbrev rawQ (z : ℚ) (n : ℕ) : ℚ[X]:=Port.Unified.ParameterFamily.Q z n
abbrev rawScale (z : ℚ) (n : ℕ) : ℚ:=Port.Unified.ParameterFamily.d z n
abbrev normScale (n : ℕ) : ℚ:=Port.Li2.Sn n^(2*n)/Port.Li2.Fn n
def W (n : ℕ) : RatFunc ℚ:=rfPoly (Port.Li2.D n)^3/rfPoly (Port.Li2.D (4*n))
def li2Lam (z : ℚ) (n : ℕ) (x : ℚ) (f : ℚ[X]) : ℚ:=
  (Port.Unified.ParameterFamily.numeratorFunctional z (4*n) ((Port.Li2.D n)^3*f)).eval x
def li2Lambda (z x : ℚ) (F : RatFunc ℚ) : ℚ:=
  (∑ i∈Finset.range ((pp F).natDegree+1),(i+1:ℚ)*(pp F).coeff i*liNeg i z)+
    ∑ j∈poleIndices F,poleRes F j*(j:ℚ)*z^(-(j:ℤ))*(x-tauK z j)
def crtPiInt (n ℓ : ℕ) (s : Fin ℓ) : ℤ[X]:=
  ∏ t∈Finset.univ.erase s,(X+C (t.val:ℤ))^(m n ℓ t)
def crtEInt (n ℓ : ℕ) (P : Ix n ℓ) : ℤ[X]:=
  (X+C (P.1.val:ℤ))^P.2.val*crtPiInt n ℓ P.1
def crtPi (n ℓ : ℕ) (s : Fin ℓ) : ℚ[X]:=(crtPiInt n ℓ s).map (Int.castRingHom ℚ)
def crtE (n ℓ : ℕ) (P : Ix n ℓ) : ℚ[X]:=(crtEInt n ℓ P).map (Int.castRingHom ℚ)
def crtT (n ℓ : ℕ) (e : Ix n ℓ≃Fin (2*n)) : Matrix (Fin (2*n)) (Fin (2*n)) ℤ:=
  fun i j=>(crtEInt n ℓ (e.symm i)).coeff j
def G (z : ℚ) (n ℓ : ℕ) (x : ℚ) : Matrix (Ix n ℓ) (Ix n ℓ) ℚ:=
  fun P Q=>li2Lam z n x (crtE n ℓ P*crtE n ℓ Q)
def lamLinear (z : ℚ) (n : ℕ) (x : ℚ) : ℚ[X]→ₗ[ℚ]ℚ where
  toFun:=li2Lam z n x
  map_add' P Q:=by
    dsimp only [li2Lam]
    rw [mul_add,Port.Unified.ParameterFamily.numeratorFunctional_add z (4*n)
      ((Port.Li2.D n)^3*P) ((Port.Li2.D n)^3*Q),eval_add]
  map_smul' c P:=by
    simp only [RingHom.id_apply,Polynomial.smul_eq_C_mul,smul_eq_mul]
    change (Port.Unified.ParameterFamily.numeratorFunctional z (4*n) ((Port.Li2.D n)^3*(C c*P))).eval x=
      c*(Port.Unified.ParameterFamily.numeratorFunctional z (4*n) ((Port.Li2.D n)^3*P)).eval x
    rw [show (Port.Li2.D n)^3*(C c*P)=C c*((Port.Li2.D n)^3*P) by ring,
      Port.Unified.ParameterFamily.numeratorFunctional_C_mul z (4*n) c ((Port.Li2.D n)^3*P),eval_mul,eval_C]
private theorem lam_entry (z x : ℚ) (n : ℕ) (i j : Fin (2*n)) :
    li2Lam z n x (X^(i.val+j.val))=
      Port.Unified.ParameterFamily.intercept z n (i.val+j.val)+x*Port.Unified.ParameterFamily.slope z n (i.val+j.val) := by
  unfold li2Lam
  rw [mul_comm ((Port.Li2.D n)^3)]
  change (Port.Unified.ParameterFamily.numeratorFunctional z (4*n) (Port.Li2.numerator n (i.val+j.val))).eval x=_
  rw [Port.Unified.ParameterFamily.numeratorFunctional_entry]
  simp only [eval_add,eval_C,eval_mul,eval_X]
theorem evalQ_eq_hankel (z x : ℚ) (n : ℕ) :
    (rawQ z n).eval x=Matrix.det (fun i j : Fin (2*n)=>li2Lam z n x (X^(i.val+j.val))) ∧
    (li2Family z).evalQ n x=normScale n*(rawQ z n).eval x ∧
    (primitiveFamily z).evalQ n x=rawScale z n*(rawQ z n).eval x ∧
    0<rawScale z n ∧ 0<normScale n := by
  refine ⟨?_,?_,?_,Port.Unified.ParameterFamily.d_pos z n,Port.Li2.Qtilde_scale_pos n⟩
  · change (Polynomial.evalRingHom x) (Port.Unified.ParameterFamily.Q z n)=_
    unfold Port.Unified.ParameterFamily.Q
    rw [RingHom.map_det]
    congr 1
    ext i j
    change (X*C (Port.Unified.ParameterFamily.slope z n (i.val+j.val))+
      C (Port.Unified.ParameterFamily.intercept z n (i.val+j.val))).eval x=
        li2Lam z n x (X^(i.val+j.val))
    rw [lam_entry,eval_add,eval_mul,eval_X,eval_C,eval_C]
    ring
  · change (Port.Unified.ParameterFamily.Qtilde z n).eval x=_
    rw [Port.Unified.ParameterFamily.Qtilde,eval_mul,eval_C]
  · change ((Port.Unified.ParameterFamily.P z n).map (algebraMap ℤ ℚ)).eval x=_
    rw [Port.Unified.ParameterFamily.P_eq_d_Q,eval_mul,eval_C]
private theorem crtE_generic (n ℓ : ℕ) (P : Ix n ℓ) :
    crtE n ℓ P=CatalanCore.Content.crtE (fun s : Fin ℓ=>-(s.val:ℚ)) (fun s=>m n ℓ s) P.1 P.2.val := by
  simp only [crtE,crtEInt,crtPiInt,CatalanCore.Content.crtE,
    Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_prod,Polynomial.map_add,
    Polynomial.map_X,Polynomial.map_C,Int.coe_castRingHom,Int.cast_natCast,map_neg,sub_neg_eq_add]
private theorem crtE_degree (n ℓ : ℕ) (e : Ix n ℓ≃Fin (2*n)) (P : Ix n ℓ) :
    (crtE n ℓ P).natDegree<2*n := by
  have hs : ∑ s : Fin ℓ,m n ℓ s=2*n:=by
    simpa only [Ix,Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr e
  rw [crtE_generic]
  simpa only [hs] using CatalanCore.Content.crtE_natDegree_lt
    (fun s : Fin ℓ=>-(s.val:ℚ)) (fun s=>m n ℓ s) P.1 P.2.val P.2.isLt
private theorem crtT_not_dvd (n ℓ : ℕ) [Fact ℓ.Prime] (e : Ix n ℓ≃Fin (2*n)) :
    ¬(ℓ:ℤ)∣(crtT n ℓ e).det := by
  let e0 : (Ix n ℓ⊕Fin 0)≃Fin (2*n):=(Equiv.sumEmpty (Ix n ℓ) (Fin 0)).trans e
  have hs : (∑ s : Fin ℓ,m n ℓ s)+0=2*n:=by
    simpa only [Ix,Fintype.card_sigma,Fintype.card_fin,add_zero] using Fintype.card_congr e
  have hi : Function.Injective (fun s : Fin ℓ=>(Int.castRingHom (ZMod ℓ)) (-(s.val:ℤ))) := by
    intro s t h
    simp only [Int.coe_castRingHom,Int.cast_neg,Int.cast_natCast,neg_inj] at h
    apply Fin.ext
    have hh:=(ZMod.natCast_eq_natCast_iff' s.val t.val ℓ).mp h
    simpa only [Nat.mod_eq_of_lt s.isLt,Nat.mod_eq_of_lt t.isLt] using hh
  have hd:=CatalanCore.Content.crt_det_not_dvd ℓ (fun s : Fin ℓ=>-(s.val:ℤ)) hi
    (fun s=>m n ℓ s) 0 (2*n) hs e0
  have hm : (Matrix.of fun (i : Fin (2*n)) (j : Fin (2*n))=>
      (CatalanCore.Content.crtFam (fun s : Fin ℓ=>-(s.val:ℤ)) (fun s=>m n ℓ s) 0 (e0.symm i)).coeff j)=
      crtT n ℓ e := by
    ext i j
    simp [e0,Equiv.sumEmpty,CatalanCore.Content.crtFam,CatalanCore.Content.crtE,
      crtT,crtEInt,crtPiInt,map_neg,sub_neg_eq_add]
  rw [hm] at hd
  exact hd
private theorem crt_gram_eq (z x : ℚ) (n ℓ : ℕ) (e : Ix n ℓ≃Fin (2*n)) :
    Matrix.det (fun P Q : Ix n ℓ=>li2Lam z n x (crtE n ℓ P*crtE n ℓ Q))=
      ((crtT n ℓ e).det:ℚ)^2*(rawQ z n).eval x := by
  classical
  let E : Fin (2*n)→ℚ[X]:=fun i=>crtE n ℓ (e.symm i)
  have hE : ∀ i,(E i).natDegree<2*n:=fun i=>crtE_degree n ℓ e (e.symm i)
  let M : Matrix (Fin (2*n)) (Fin (2*n)) ℚ[X]:=
    Matrix.of (fun a b=>Port.Unified.ParameterFamily.numeratorFunctional z (4*n) ((Port.Li2.D n)^3*E a*E b))
  have hpoly : M.det=C ((Port.Li2.coeffMat E).det^2)*rawQ z n :=
    Port.Unified.ParameterFamily.original_gram_basis_change z n E hE
  have hmat : (Polynomial.evalRingHom x).mapMatrix M=
      Matrix.of (fun a b=>li2Lam z n x (E a*E b)) := by
    ext a b
    change (Port.Unified.ParameterFamily.numeratorFunctional z (4*n) ((Port.Li2.D n)^3*E a*E b)).eval x=
      (Port.Unified.ParameterFamily.numeratorFunctional z (4*n) ((Port.Li2.D n)^3*(E a*E b))).eval x
    rw [mul_assoc]
  have heval : (Matrix.of fun a b=>li2Lam z n x (E a*E b)).det=
      (Port.Li2.coeffMat E).det^2*(rawQ z n).eval x := by
    calc
      _=(Polynomial.evalRingHom x) M.det:=by rw [RingHom.map_det,hmat]
      _=(Polynomial.evalRingHom x) (C ((Port.Li2.coeffMat E).det^2)*rawQ z n):=congrArg _ hpoly
      _=_:=by change (C ((Port.Li2.coeffMat E).det^2)*rawQ z n).eval x=_;rw [eval_mul,eval_C]
  have ht : Port.Li2.coeffMat E=(crtT n ℓ e).map (Int.castRingHom ℚ) := by
    ext i j
    change (crtE n ℓ (e.symm i)).coeff j=(Int.castRingHom ℚ) ((crtEInt n ℓ (e.symm i)).coeff j)
    rw [crtE,Polynomial.coeff_map]
  have htd : (Port.Li2.coeffMat E).det=((crtT n ℓ e).det:ℚ) := by
    rw [ht,Int.coe_castRingHom,←Int.cast_det]
  have hre:=Matrix.det_submatrix_equiv_self e.symm
    (Matrix.of fun P Q : Ix n ℓ=>li2Lam z n x (crtE n ℓ P*crtE n ℓ Q))
  calc
    _=(Matrix.of fun a b=>li2Lam z n x (E a*E b)).det:=hre.symm
    _=(Port.Li2.coeffMat E).det^2*(rawQ z n).eval x:=heval
    _=_:=by rw [htd]
theorem crt_gram_bridge (z x : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hR : Range n ℓ) (e : Ix n ℓ≃Fin (2*n)) :
    ¬(ℓ:ℤ)∣(crtT n ℓ e).det ∧
      Matrix.det (fun P Q : Ix n ℓ=>li2Lam z n x (crtE n ℓ P*crtE n ℓ Q))=
        ((crtT n ℓ e).det:ℚ)^2*(rawQ z n).eval x ∧
      (Matrix.det (fun P Q : Ix n ℓ=>li2Lam z n x (crtE n ℓ P*crtE n ℓ Q))≠0→
        (primitiveFamily z).evalQ n x≠0) := by
  refine ⟨crtT_not_dvd n ℓ e,crt_gram_eq z x n ℓ e,?_⟩
  intro hG
  have hQ : (rawQ z n).eval x≠0:=by
    intro hz
    apply hG
    rw [crt_gram_eq z x n ℓ e,hz,mul_zero]
  have hh:=evalQ_eq_hankel z x n
  rw [hh.2.2.1]
  exact mul_ne_zero hh.2.2.2.1.ne' hQ

private def fullMoment (z : ℚ) (P : ℚ[X]) : ℚ:=P.eval 0+Port.Li2.parameterG z P
private theorem parameterG_sub (z : ℚ) (P Q : ℚ[X]) :
    Port.Li2.parameterG z (P-Q)=Port.Li2.parameterG z P-Port.Li2.parameterG z Q := by
  rw [show P-Q=P+C (-1)*Q by simp [sub_eq_add_neg],Port.Li2.parameterG_add,Port.Li2.parameterG_C_mul]
  ring
private theorem parameterG_shift_minus (z : ℚ) (hz : z≠1) (P : ℚ[X]) :
    Port.Li2.parameterG z (P.comp (X-1))=z*fullMoment z P := by
  have he : ((X:ℚ[X])-1).comp (X+1)=X:=by simp
  have hc : (P.comp (X-1)).comp (X+1)=P:=by rw [comp_assoc,he,comp_X]
  have hv : (P.comp (X-1)).eval 1=P.eval 0:=by simp
  have hh:=Port.Li2.parameterG_shift_one z hz (P.comp (X-1))
  rw [hc,hv] at hh
  dsimp [fullMoment]
  linear_combination -hh
private theorem fullMoment_desc_step (z : ℚ) (hz : z≠1) (n : ℕ) :
    (1-z)*fullMoment z (descPochhammer ℚ (n+1))=
      z*(n+1)*fullMoment z (descPochhammer ℚ n) := by
  have hh:=congrArg (Port.Li2.parameterG z) (descPochhammer_succ_comp_X_sub_one ℚ n)
  have hn : (n+(1:ℚ[X]))=C ((n:ℚ)+1):=by simp
  simp only [smul_eq_mul,hn,parameterG_sub,Port.Li2.parameterG_C_mul,
    parameterG_shift_minus z hz] at hh
  have h0 : (descPochhammer ℚ (n+1)).eval 0=0:=by simp
  have hL : Port.Li2.parameterG z (descPochhammer ℚ (n+1))=
      fullMoment z (descPochhammer ℚ (n+1)):=by simp [fullMoment,h0]
  rw [hL] at hh
  linear_combination -hh
private theorem fullMoment_desc (z : ℚ) (hz : z≠1) (n : ℕ) :
    fullMoment z (descPochhammer ℚ n)=(n.factorial:ℚ)*z^n/(1-z)^(n+1) := by
  have hd : 1-z≠0:=sub_ne_zero.mpr (Ne.symm hz)
  induction n with
  | zero =>
    have hg : Port.Li2.parameterG z 1=Port.Li2.parameterMoment z 0:=by
      simpa using Port.Li2.parameterG_C_mul_X_pow z 1 0
    simp only [descPochhammer_zero,fullMoment,eval_one,hg,Port.Li2.parameterMoment,
      Nat.factorial_zero,Nat.cast_one,pow_zero,pow_one,one_mul]
    field_simp
    ring
  | succ n ih =>
    have hh:=fullMoment_desc_step z hz n
    have hr : fullMoment z (descPochhammer ℚ (n+1))=
        z*(n+1)*fullMoment z (descPochhammer ℚ n)/(1-z) := by
      apply (eq_div_iff hd).mpr
      linear_combination hh
    rw [hr,ih,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp
    ring
private theorem pow_stirling_desc (k : ℕ) :
    (X:ℚ[X])^k=∑ i∈Finset.range (k+1),C (Nat.stirlingSecond k i:ℚ)*descPochhammer ℚ i := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun n : ℕ=>(n:ℚ)):=Nat.cast_injective
  refine (Set.infinite_range_of_injective hi).mono ?_
  rintro x ⟨n,rfl⟩
  change ((X:ℚ[X])^k).eval (n:ℚ)=
    (∑ i∈Finset.range (k+1),C (Nat.stirlingSecond k i:ℚ)*descPochhammer ℚ i).eval (n:ℚ)
  simp only [eval_pow,eval_X,eval_finset_sum,eval_mul,eval_C,descPochhammer_eval_eq_descFactorial]
  exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n k
private theorem fullMoment_sum_C {ι : Type*} (z : ℚ) (S : Finset ι) (a : ι→ℚ) (P : ι→ℚ[X]) :
    fullMoment z (∑ i∈S,C (a i)*P i)=∑ i∈S,a i*fullMoment z (P i) := by
  classical
  unfold fullMoment
  rw [eval_finset_sum,Port.Li2.parameterG_sum]
  simp only [eval_mul,eval_C,Port.Li2.parameterG_C_mul]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring
private theorem fullMoment_X_pow (z : ℚ) (n : ℕ) :
    fullMoment z (X^n)=(if n=0 then 1 else 0)+Port.Li2.parameterMoment z n := by
  have hg : Port.Li2.parameterG z (X^n)=Port.Li2.parameterMoment z n:=by
    simpa using Port.Li2.parameterG_C_mul_X_pow z 1 n
  unfold fullMoment
  rw [hg,eval_pow,eval_X]
  by_cases hn : n=0 <;> simp [hn]
/-- The finite Stirling formula is exactly the ported parameter moment, for every
rational z≠1. No analytic convergence hypothesis is added. -/
theorem liNeg_eq_parameterMoment (z : ℚ) (hz : z≠1) (n : ℕ) :
    liNeg n z=Port.Li2.parameterMoment z n := by
  classical
  cases n with
  | zero => simp [liNeg,Port.Li2.parameterMoment]
  | succ n =>
    have hh:=congrArg (fullMoment z) (pow_stirling_desc (n+1))
    rw [fullMoment_X_pow,fullMoment_sum_C] at hh
    simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,zero_add] at hh
    simp_rw [fullMoment_desc z hz] at hh
    let f : ℕ→ℚ:=fun i=>(Nat.stirlingSecond (n+1) i:ℚ)*(i.factorial:ℚ)*z^i/(1-z)^(i+1)
    have hsum : Port.Li2.parameterMoment z (n+1)=∑ i∈Finset.range (n+2),f i := by
      convert hh using 1
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [f]
      ring
    have hsub : Finset.Icc 1 (n+1)⊆Finset.range (n+2):=by
      intro i hi
      obtain ⟨hlo,hhi⟩:=Finset.mem_Icc.mp hi
      apply Finset.mem_range.mpr
      omega
    have he : (∑ i∈Finset.Icc 1 (n+1),f i)=∑ i∈Finset.range (n+2),f i := by
      apply Finset.sum_subset hsub
      intro i hi hn
      have hi0 : i=0:=by
        have hupper:=Finset.mem_range.mp hi
        have hnot : ¬ (1 ≤ i ∧ i ≤ n+1):=by simpa only [Finset.mem_Icc] using hn
        omega
      subst i
      simp [f]
    rw [liNeg,if_neg (by omega : n+1≠0)]
    exact he.trans hsum.symm
private theorem canonical_functional (P : ℚ[X]) (S : Finset ℕ)
    (φ : ℚ[X]→ℚ) (ψ : ℕ→ℚ) :
    let F:=rfPoly P/rfPoly (poleProd S)
    φ (pp F)+(∑ m∈poleIndices F,poleRes F m*ψ m)=
      φ (P /ₘ poleProd S)+∑ m∈S,poleCoeff P S m*ψ m := by
  classical
  let F:=rfPoly P/rfPoly (poleProd S)
  have hc:=fraction_coefficients P S
  have hdiv : F.denom∣poleProd S:=RatFunc.denom_div_dvd P (poleProd S)
  obtain ⟨hD,hI⟩:=canonical_poles F S hdiv
  have hsub : poleIndices F⊆S:=by rw [hI];exact Finset.filter_subset _ _
  change φ (pp F)+(∑ m∈poleIndices F,poleRes F m*ψ m)=
    φ (P /ₘ poleProd S)+∑ m∈S,poleCoeff P S m*ψ m
  rw [hc.1]
  congr 1
  let f : ℕ→ℚ:=fun m=>(if m∈poleIndices F then poleRes F m else 0)*ψ m
  calc
    (∑ m∈poleIndices F,poleRes F m*ψ m)=∑ m∈poleIndices F,f m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [f,if_pos hm]
    _=∑ m∈S,f m:=Finset.sum_subset hsub (fun m hmS hmI=>by simp [f,hmI])
    _=∑ m∈S,poleCoeff P S m*ψ m := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp only [f]
      rw [hc.2 m hm]
private theorem parameterU_formula (z : ℚ) (hz : z≠1) (P : ℚ[X]) :
    Port.Li2.parameterG z (X*P).derivative=
      ∑ i∈Finset.range (P.natDegree+1),(i+1:ℚ)*P.coeff i*liNeg i z := by
  let f : ℕ→ℚ→ℚ:=fun i a=>(i+1:ℚ)*a*liNeg i z
  have hpoly : ∀ P : ℚ[X],Port.Li2.parameterG z (X*P).derivative=P.sum f := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      rw [mul_add,derivative_add,Port.Li2.parameterG_add,hP,hQ]
      symm
      exact Polynomial.sum_add_index _ _ _ (fun i=>by simp [f]) (fun i a b=>by dsimp [f];ring)
    | monomial i a =>
      simp only [X_mul_monomial,derivative_monomial_succ,Port.Li2.parameterG_monomial]
      rw [Polynomial.sum_monomial_index a f (by simp [f])]
      dsimp [f]
      rw [liNeg_eq_parameterMoment z hz]
      ring
  rw [hpoly]
  simpa only [f] using (Polynomial.sum_over_range P (f:=f) (fun i=>by simp [f]))

private theorem pole_derivative (S : Finset ℕ) (m : ℕ) (hm : m∈S) :
    (poleProd S).derivative.eval (-(m:ℚ))=∏ n∈S.erase m,((n:ℚ)-m) := by
  classical
  have hp : poleProd S=(X+C (m:ℚ))*poleProd (S.erase m) :=
    (Finset.mul_prod_erase S (fun m : ℕ=>X+C (m:ℚ)) hm).symm
  rw [hp]
  simp [poleProd,derivative_mul,eval_prod,sub_eq_add_neg,add_comm]
private theorem li2Lambda_fraction (z x : ℚ) (P : ℚ[X]) (S : Finset ℕ) :
    li2Lambda z x (rfPoly P/rfPoly (poleProd S))=
      (∑ i∈Finset.range ((P /ₘ poleProd S).natDegree+1),
        (i+1:ℚ)*(P /ₘ poleProd S).coeff i*liNeg i z)+
      ∑ m∈S,poleCoeff P S m*(m:ℚ)*z^(-(m:ℤ))*(x-tauK z m) := by
  simpa only [li2Lambda,mul_assoc] using canonical_functional P S
    (fun Q=>∑ i∈Finset.range (Q.natDegree+1),(i+1:ℚ)*Q.coeff i*liNeg i z)
    (fun m=>(m:ℚ)*z^(-(m:ℤ))*(x-tauK z m))
private theorem numeratorFunctional_evalRF (z x : ℚ) (hz : z≠1) (m : ℕ) (P : ℚ[X]) :
    (Port.Unified.ParameterFamily.numeratorFunctional z m P).eval x=
      li2Lambda z x (rfPoly P/rfPoly (Port.Li2.D m)) := by
  classical
  rw [show Port.Li2.D m=poleProd (Finset.Icc 1 m) from rfl,li2Lambda_fraction]
  unfold Port.Unified.ParameterFamily.numeratorFunctional
  rw [eval_add,eval_C,eval_finset_sum]
  congr 1
  · exact parameterU_formula z hz (P /ₘ poleProd (Finset.Icc 1 m))
  · apply Finset.sum_congr rfl
    intro j hj
    rw [eval_mul,eval_C,eval_mul,eval_C,eval_sub,eval_X,eval_C,
      poleCoeff,pole_derivative _ _ hj]
    have ht : Port.Li2.parameterTau z j=tauK z j:=rfl
    rw [ht,_root_.zpow_neg,zpow_natCast,inv_pow]
    ring
theorem lam_linear_and_F0 (z x : ℚ) (hz : z≠0) (h1 : z≠1) (n : ℕ) :
    (∃ f : ℚ[X]→ₗ[ℚ]ℚ,∀P,f P=li2Lam z n x P) ∧
      ∀P,li2Lam z n x P=li2Lambda z x (W n*rfPoly P) := by
  refine ⟨⟨lamLinear z n x,fun P=>rfl⟩,?_⟩
  intro P
  have he : W n*rfPoly P=rfPoly ((Port.Li2.D n)^3*P)/rfPoly (Port.Li2.D (4*n)) := by
    simp only [W,rfPoly,map_mul,map_pow]
    ring
  rw [he]
  exact numeratorFunctional_evalRF z x h1 (4*n) ((Port.Li2.D n)^3*P)

#print axioms evalQ_eq_hankel
#print axioms crt_gram_bridge
#print axioms liNeg_eq_parameterMoment
#print axioms lam_linear_and_F0
end
end CatalanCore.Li2.NV


