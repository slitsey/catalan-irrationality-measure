module
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialLists
public import CatalanCore.Li2.NVMod.DataSupport.ClearedSource
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1500000
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.DataSupport
noncomputable section
variable {R : Type*} [CommRing R]
def monomialCoefficients (e : ℕ) (a : R) : List R := List.replicate e 0++[a]
theorem monomialCoefficients_spec (e : ℕ) (a : R) :
    coefficientsPoly (monomialCoefficients e a)=C a*X^e := by
  induction e with
  | zero=>simp [monomialCoefficients,coefficientsPoly]
  | succ e ih=>
    simp only [monomialCoefficients,List.replicate_succ,List.cons_append,coefficientsPoly,map_zero,zero_add] at *
    rw [ih,pow_succ]
    ring

def sumCoefficients : List (List R)→List R
  | []=>[]
  | a::as=>coefficientsAdd a (sumCoefficients as)
theorem sumCoefficients_spec (xs : List (List R)) :
    coefficientsPoly (sumCoefficients xs)=(xs.map coefficientsPoly).sum := by
  induction xs with
  | nil=>simp [sumCoefficients,coefficientsPoly]
  | cons a as ih=>simp [sumCoefficients,coefficientsPoly_add,ih]

def powerCoefficients : ℕ→List R→List R
  | 0,_=>[1]
  | n+1,xs=>coefficientsMul xs (powerCoefficients n xs)
theorem powerCoefficients_spec (n : ℕ) (xs : List R) :
    coefficientsPoly (powerCoefficients n xs)=(coefficientsPoly xs)^n := by
  induction n with
  | zero=>simp [powerCoefficients,coefficientsPoly]
  | succ n ih=>simp only [powerCoefficients,coefficientsPoly_mul,ih,pow_succ']

theorem shifted_range_sum {S : Type*} [AddCommMonoid S] (f : ℕ→S) (m : ℕ) :
    ((List.range m).map (fun b=>f (b+1))).sum=∑ b∈Icc 1 m,f b := by
  induction m with
  | zero=>simp
  | succ m ih=>
    rw [List.range_succ,List.map_append,List.sum_append,ih,
      Finset.sum_Icc_succ_top (by omega : 1≤m+1)]
    simp

def omegaCoefficients (cutoff m : ℕ) : List ℚ :=
  sumCoefficients ((List.range m).map (fun b=>monomialCoefficients (cutoff+(b+1)-m) (1/((b+1:ℕ):ℚ)^2)))

def liCoefficients (order j : ℕ) : List ℚ :=
  if j=0 then coefficientsMul [0,1] (powerCoefficients (order-1) [1,-1])
  else sumCoefficients ((List.range j).map (fun b=>
    coefficientsMul (monomialCoefficients (b+1) ((Nat.stirlingSecond j (b+1):ℚ)*((b+1).factorial:ℚ)))
      (powerCoefficients (order-((b+1)+1)) [1,-1])))

theorem omegaCoefficients_spec (cutoff m : ℕ) :
    coefficientsPoly (omegaCoefficients cutoff m)=omegaNumerator cutoff m := by
  simp only [omegaCoefficients,sumCoefficients_spec,List.map_map,Function.comp_def,
    monomialCoefficients_spec,omegaNumerator]
  exact shifted_range_sum (fun b=>C (1/(b:ℚ)^2)*X^(cutoff+b-m)) m

theorem liCoefficients_spec (order j : ℕ) :
    coefficientsPoly (liCoefficients order j)=liNumerator order j := by
  by_cases hj : j=0
  · subst j
    simp [liCoefficients,liNumerator,coefficientsPoly_mul,powerCoefficients_spec,
      coefficientsPoly]
    ring
  · simp [liCoefficients,liNumerator,hj,sumCoefficients_spec,List.map_map,
      coefficientsPoly_mul,monomialCoefficients_spec,powerCoefficients_spec,
      coefficientsPoly,Function.comp_def,sub_eq_add_neg]
    exact shifted_range_sum (fun b=>(Nat.stirlingSecond j b:ℚ[X])*(b.factorial:ℚ[X])*
      X^b*(1+ -X)^(order-(b+1))) j
/-- A supplied quotient/remainder equality is checked on lists; this theorem
then binds the quotient to the original monic division in the source formula. -/
theorem quotient_from_lists (A : TypeKey) (e : ℕ) (q r : List ℤ)
    (heq : coefficientsPoly r+denominatorZ A*coefficientsPoly q=X^e*numeratorZ A)
    (hdeg : (coefficientsPoly r).degree<(denominatorZ A).degree) :
    (coefficientsPoly q).map (Int.castRingHom ℚ)=polyPart A (X^e) := by
  have h := Polynomial.div_modByMonic_unique (coefficientsPoly q) (coefficientsPoly r)
    (denominatorZ_monic A) ⟨heq,hdeg⟩
  rw [←quotientK_Q,←quotientZ_map]
  congr 1
  exact h.1.symm
#print axioms quotient_from_lists
end
end CatalanCore.Li2.NVMod.DataSupport
