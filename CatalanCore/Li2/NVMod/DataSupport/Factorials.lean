module
public import CatalanCore.Li2.NVMod.ResBase
public import Mathlib.LinearAlgebra.Vandermonde
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1200000
open Polynomial Finset Matrix
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.DataSupport
noncomputable section

theorem vandermonde_nat_det (n : ℕ) :
    (Matrix.vandermonde (fun i : Fin n => (i.val:ℚ))).det=
      ∏ i : Fin n,(i.val.factorial:ℚ) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Matrix.det_vandermonde_id_eq_superFactorial]
    rw [show (∏ i : Fin (n+1),(i.val.factorial:ℚ))=
        ∏ i∈Finset.range (n+1),(i.factorial:ℚ) from
      Fin.prod_univ_eq_prod_range (fun i : ℕ=>(i.factorial:ℚ)) (n+1)]
    exact_mod_cast (Nat.prod_range_succ_factorial n).symm

theorem factorialHankel_det (n γ : ℕ) :
    (factorialHankel n γ).det=
      ∏ k : Fin n,(Nat.factorial k.val:ℚ)*(Nat.factorial (k.val+γ):ℚ) := by
  let v : Fin n→ℚ := fun i=>(i.val:ℚ)+(γ:ℚ)+1
  let P : Fin n→ℚ[X] := fun j=>ascPochhammer ℚ j.val
  have he (i j : Fin n) :
      (Nat.factorial (i.val+j.val+γ):ℚ)=
        (Nat.factorial (i.val+γ):ℚ)*(P j).eval (v i) := by
    dsimp only [P,v]
    rw [show (i.val:ℚ)+(γ:ℚ)+1=((i.val+γ+1:ℕ):ℚ) by push_cast;ring]
    rw [ascPochhammer_nat_eq_natCast_ascFactorial]
    norm_cast
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (Nat.factorial_mul_ascFactorial (i.val+γ) j.val).symm
  have hm : factorialHankel n γ=
      Matrix.of (fun i j=>(Nat.factorial (i.val+γ):ℚ)*(P j).eval (v i)) := by
    ext i j
    exact he i j
  have hd : (Matrix.of (fun i j : Fin n=>
      (Nat.factorial (i.val+γ):ℚ)*(P j).eval (v i))).det =
      (∏ i : Fin n,(Nat.factorial (i.val+γ):ℚ))*
        (Matrix.of (fun i j : Fin n=>(P j).eval (v i))).det := by
    simpa only [Matrix.of_apply] using
      Matrix.det_mul_column (fun i : Fin n=>(Nat.factorial (i.val+γ):ℚ))
        (Matrix.of (fun i j : Fin n=>(P j).eval (v i)))
  rw [hm,hd]
  have hv := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v P
    (fun j=>ascPochhammer_natDegree ℚ j.val) (fun j=>monic_ascPochhammer ℚ j.val)
  rw [←hv]
  have hshift : (Matrix.vandermonde v).det=
      (Matrix.vandermonde (fun i : Fin n=>(i.val:ℚ))).det := by
    dsimp only [v]
    simpa only [add_assoc] using
      Matrix.det_vandermonde_add (fun i : Fin n=>(i.val:ℚ)) ((γ:ℚ)+1)
  rw [hshift,vandermonde_nat_det,Finset.prod_mul_distrib]
  ring

theorem allFactorials (A : TypeKey) : FactorialDetChecked A := by
  intro n hn γ hγ
  exact factorialHankel_det n γ
#print axioms factorialHankel_det
#print axioms allFactorials
end
end CatalanCore.Li2.NVMod.DataSupport
