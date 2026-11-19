module
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialSourceLists
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialSourceEngine
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.DataSupport
noncomputable section

theorem list_product_polynomial (xs : List ℕ) (hn : xs.Nodup) :
    coefficientsPoly (linearProductCoefficients (xs.map (fun j : ℕ=>(j:ℤ))))=
      ∏ j∈xs.toFinset,(X+C (j:ℤ)) := by
  rw [linearProductCoefficients_spec,List.map_map]
  simpa only [Function.comp_def] using
    (List.prod_toFinset (fun j : ℕ=>X+C (j:ℤ)) hn).symm

def baseIndices (A : TypeKey) : Finset ℕ :=
  match A.kind with
  | .V=>range A.a
  | .U=>Icc 1 A.a

def numeratorCoefficients (kind : Kind) (xs : List ℕ) : List ℤ :=
  let q:=linearProductCoefficients (xs.map (fun j : ℕ=>(j:ℤ)))
  match kind with
  | .V=>coefficientsMul q q
  | .U=>coefficientsMul [0,1] (coefficientsMul q q)

theorem numeratorCoefficients_spec (A : TypeKey) (xs : List ℕ)
    (hn : xs.Nodup) (hs : xs.toFinset=baseIndices A) :
    coefficientsPoly (numeratorCoefficients A.kind xs)=numeratorZ A := by
  have hp := list_product_polynomial xs hn
  rw [hs] at hp
  cases hk : A.kind <;>
    simp only [numeratorCoefficients,hk,coefficientsPoly_mul,hp,baseIndices,numeratorZ,
      coefficientsPoly,map_zero,map_one,zero_add,mul_zero,add_zero,mul_one] <;>
    rw [Finset.prod_pow] <;> ring

theorem denominatorCoefficients_spec (A : TypeKey) (xs : List ℕ)
    (hn : xs.Nodup) (hs : xs.toFinset=poles A) :
    coefficientsPoly (linearProductCoefficients (xs.map (fun j : ℕ=>(j:ℤ))))=denominatorZ A := by
  rw [list_product_polynomial xs hn,hs]
  rfl

theorem coefficient_horner {R : Type*} [CommRing R] (xs : List R) (x : R) :
    (coefficientsPoly xs).eval x=xs.foldr (fun c acc=>c+x*acc) 0 := by
  induction xs with
  | nil=>simp [coefficientsPoly]
  | cons a as ih=>simp [coefficientsPoly,ih]

/-- The residue source is checked once per pole using the supplied integer numerator. -/
theorem residue_integer_source (A : TypeKey) (xs : List ℤ)
    (hx : coefficientsPoly xs=numeratorZ A) (m : ℕ) :
    residue A m=
      (((xs.foldr (fun c acc=>c+(-(m:ℤ))*acc) 0:ℤ):ℚ)/
        (((denominatorZ A).derivative.eval (-(m:ℤ)):ℤ):ℚ)) := by
  rw [residue,←numeratorK_Q,←denominatorK_Q,denominatorK_deriv_eval_int]
  have hn := map_eval_int ℚ (coefficientsPoly xs) (-(m:ℤ))
  rw [hx,numeratorZ_map] at hn
  rw [show (-(m:ℚ))=((-(m:ℤ):ℤ):ℚ) by simp,hn,←hx,coefficient_horner]

def evalAndDerivative {R : Type*} [CommRing R] (x : R) : List R→R×R
  | []=>(0,0)
  | a::as=>let z:=evalAndDerivative x as;(a+x*z.1,z.1+x*z.2)

theorem evalAndDerivative_spec {R : Type*} [CommRing R] (xs : List R) (x : R) :
    (evalAndDerivative x xs).1=(coefficientsPoly xs).eval x ∧
    (evalAndDerivative x xs).2=(coefficientsPoly xs).derivative.eval x := by
  induction xs with
  | nil=>simp [evalAndDerivative,coefficientsPoly]
  | cons a as ih=>
    constructor <;>
      simp [evalAndDerivative,coefficientsPoly,Polynomial.derivative_mul,ih.1,ih.2] <;> ring

theorem residue_from_tables (A : TypeKey) (num den : List ℤ)
    (hn : coefficientsPoly num=numeratorZ A) (hd : coefficientsPoly den=denominatorZ A) (m : ℕ) :
    residue A m=(((evalAndDerivative (-(m:ℤ)) num).1:ℚ)/
      ((evalAndDerivative (-(m:ℤ)) den).2:ℚ)) := by
  rw [residue_integer_source A num hn m,←hd,←coefficient_horner num (-(m:ℤ)),
    ←(evalAndDerivative_spec num (-(m:ℤ))).1,←(evalAndDerivative_spec den (-(m:ℤ))).2]

theorem coefficientsPoly_append_zero {R : Type*} [CommRing R] (xs : List R) (n : ℕ) :
    coefficientsPoly (xs++List.replicate n 0)=coefficientsPoly xs := by
  induction xs with
  | nil=>
    induction n with
    | zero=>rfl
    | succ n ih=>simpa [coefficientsPoly,List.replicate_succ] using ih
  | cons a as ih=>
    simp only [List.cons_append,coefficientsPoly]
    rw [ih]

def padCoefficients {R : Type*} [Zero R] (n : ℕ) (xs : List R) : List R :=
  xs++List.replicate (n-xs.length) 0

theorem padCoefficients_spec {R : Type*} [CommRing R] (n : ℕ) (xs : List R) :
    coefficientsPoly (padCoefficients n xs)=coefficientsPoly xs :=
  coefficientsPoly_append_zero xs _

theorem weightDen_degree (A : TypeKey) : (weightDen A).natDegree=A.c-A.a := by
  rw [weightDen,Polynomial.natDegree_prod_of_monic _ _ (fun (m : ℕ) hm=>Polynomial.monic_X_add_C (m:ℚ))]
  simp only [Polynomial.natDegree_X_add_C]
  cases hk : A.kind <;> simp [poleSet,hk]

theorem weightNum_degree (A : TypeKey) :
    (weightNum A).natDegree=if A.kind=.U then 2*A.a+1 else 2*A.a := by
  have hp (S : Finset ℕ) : (∏ j∈S,(X+C (j:ℚ))^2).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun (j : ℕ) hj=>(Polynomial.monic_X_add_C (j:ℚ)).pow 2)
  cases hk : A.kind
  · simp only [weightNum,hk,reduceCtorEq,ite_false]
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun (j : ℕ) hj=>(Polynomial.monic_X_add_C (j:ℚ)).pow 2)]
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_add_C,mul_one]
    simp [mul_comm]
  · simp only [weightNum,hk,ite_true]
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (hp _).ne_zero,
      Polynomial.natDegree_prod_of_monic _ _ (fun (j : ℕ) hj=>(Polynomial.monic_X_add_C (j:ℚ)).pow 2)]
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_add_C,Polynomial.natDegree_X,mul_one]
    simp [mul_comm,add_comm]

theorem h0_formula (A : TypeKey) :
    h0 A=((A.c-A.a:ℕ):ℤ)-(if A.kind=.U then (2*A.a+1:ℕ) else 2*A.a) := by
  rw [h0,weightDen_degree,weightNum_degree]

theorem denominatorZ_natDegree (A : TypeKey) : (denominatorZ A).natDegree=A.c-A.a := by
  rw [denominatorZ,Polynomial.natDegree_prod_of_monic _ _
    (fun (m : ℕ) hm=>Polynomial.monic_X_add_C (m:ℤ))]
  simp only [Polynomial.natDegree_X_add_C]
  cases hk : A.kind <;> simp [poles,hk]

theorem coefficients_natDegree_bound {R : Type*} [CommRing R] (xs : List R) (d : ℕ)
    (h : xs.length≤d+1) : (coefficientsPoly xs).natDegree≤d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coefficientsPoly_coeff]
  exact List.getD_eq_default _ _ (by omega)

def quotientCheck (n L e : ℕ) (num den q r : List ℤ) : Bool :=
  decide (r.length≤n) && decide
    (padCoefficients L (coefficientsAdd r (coefficientsMul den q))=
      padCoefficients L (coefficientsMul (monomialCoefficients e 1) num))

theorem quotient_from_check (A : TypeKey) (L e : ℕ) (num den q r : List ℤ)
    (hn : coefficientsPoly num=numeratorZ A) (hd : coefficientsPoly den=denominatorZ A)
    (hc : quotientCheck (A.c-A.a) L e num den q r=true) :
    (coefficientsPoly q).map (Int.castRingHom ℚ)=polyPart A (X^e) := by
  have hh : r.length≤A.c-A.a ∧
      padCoefficients L (coefficientsAdd r (coefficientsMul den q))=
      padCoefficients L (coefficientsMul (monomialCoefficients e 1) num) := by
    simpa [quotientCheck] using hc
  have he := congrArg (coefficientsPoly (R:=ℤ)) hh.2
  simp only [padCoefficients_spec,coefficientsPoly_add,coefficientsPoly_mul,
    monomialCoefficients_spec,map_one,one_mul] at he
  rw [hn,hd] at he
  apply quotient_from_lists A e q r he
  rw [Polynomial.degree_eq_natDegree (denominatorZ_monic A).ne_zero,denominatorZ_natDegree]
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro j hj
  rw [coefficientsPoly_coeff]
  exact List.getD_eq_default _ _ (by omega)

def momentCheck (L : ℕ) (ms : List ℕ) (rho : ℕ→ℚ) (qs zs : List ℤ)
    (e D cutoff order : ℕ) : Bool :=
  decide (padCoefficients L (zs.map (fun (z : ℤ)=>(z:ℚ)))=
    padCoefficients L (clearedCoefficients ms rho (qs.map (fun (z : ℤ)=>(z:ℚ))) e D cutoff order))

theorem moment_from_check (A : TypeKey) (L : ℕ) (ms : List ℕ) (rho : ℕ→ℚ)
    (qs zs : List ℤ) (e D cutoff order : ℕ)
    (hN : ms.Nodup) (hS : ms.toFinset=poleSet A)
    (hrho : ∀ m∈ms.toFinset,rho m=residue A m)
    (hQ : (coefficientsPoly qs).map (Int.castRingHom ℚ)=polyPart A (X^e))
    (hcut : ∀ m∈ms.toFinset,m≤cutoff) (horder : qs.length≤order+1)
    (hc : momentCheck L ms rho qs zs e D cutoff order=true) :
    intPolyRF (coefficientsPoly zs)=rfPoly (C (D:ℚ))*rfX^cutoff*(1-rfX)^order*
      momentRF A (X^e) := by
  have he : padCoefficients L (zs.map (fun (z : ℤ)=>(z:ℚ)))=
      padCoefficients L (clearedCoefficients ms rho (qs.map (fun (z : ℤ)=>(z:ℚ))) e D cutoff order) :=
    of_decide_eq_true hc
  have hp:=congrArg (coefficientsPoly (R:=ℚ)) he
  simp only [padCoefficients_spec,clearedCoefficients_spec ms hN] at hp
  change rfPoly ((coefficientsPoly zs).map (Int.castRingHom ℚ))=_
  rw [coefficientsPoly_map]
  change rfPoly (coefficientsPoly (zs.map (fun (z : ℤ)=>(z:ℚ))))=_
  rw [hp]
  apply clearedSourcePoly_spec A ms.toFinset rho
    (coefficientsPoly (qs.map (fun (z : ℤ)=>(z:ℚ)))) e D cutoff order hS hrho ?_ hcut ?_
  · simpa only [coefficientsPoly_map,Int.coe_castRingHom] using hQ.symm
  · apply coefficients_natDegree_bound
    simpa using horder

#print axioms quotient_from_check
#print axioms moment_from_check
#print axioms residue_from_tables
#print axioms h0_formula
#print axioms numeratorCoefficients_spec
#print axioms denominatorCoefficients_spec
#print axioms residue_integer_source
end
end CatalanCore.Li2.NVMod.DataSupport
