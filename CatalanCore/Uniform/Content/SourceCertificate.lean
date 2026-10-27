module
public import CatalanCore.Uniform.Content.RowCertificate
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content
open Matrix

def rowNormalization : Int → List Int → List Int → List Int → Bool
  | D,a::as,b::bs,c::cs => decide (D*a=c*b) && rowNormalization D as bs cs
  | _,[],[],[] => true
  | _,_,_,_ => false

theorem rowNormalization_sound (D : Int) (a b c : List Int)
    (hc : rowNormalization D a b c=true) (j : Nat) :
    D*a.getD j 0=c.getD j 0*b.getD j 0 := by
  induction a generalizing b c j with
  | nil => cases b <;> cases c <;> simp_all [rowNormalization,List.getD]
  | cons x xs ih =>
    cases b with
    | nil => cases c <;> simp_all [rowNormalization]
    | cons y ys =>
      cases c with
      | nil => simp_all [rowNormalization]
      | cons z zs =>
        have hh : decide (D*x=z*y)=true ∧ rowNormalization D xs ys zs=true := by
          simpa only [rowNormalization,Bool.and_eq_true] using hc
        cases j with
        | zero => simpa only [List.getD_cons_zero] using of_decide_eq_true hh.1
        | succ j => simpa only [List.getD_cons_succ] using ih ys zs hh.2 j

variable (K : Type*) [Field K]
def sourceFractions {m n : Nat} (nums dens : Fin m → List Int) :
    Matrix (Fin m) (Fin n) K :=
  fun i j => ((nums i).getD j.val 0 : K)/((dens i).getD j.val 0 : K)

theorem sourceRows_normalize {m n : Nat} (nums dens B : Fin m → List Int)
    (D : Fin m → Int) (hc : ∀ i, rowNormalization (D i) (nums i) (dens i) (B i)=true)
    (hd : ∀ i (j : Fin n), ((dens i).getD j.val 0 : K)≠0)
    (hD : ∀ i, (D i : K)≠0) :
    (sourceFractions K nums dens : Matrix (Fin m) (Fin n) K)=
      Matrix.diagonal (fun i => (D i : K)⁻¹)*castMatrix K (fromRows B) := by
  ext i j
  simp only [sourceFractions,Matrix.diagonal_mul,castMatrix,fromRows]
  have hi : (D i : K)*((nums i).getD j.val 0 : K)=
      ((B i).getD j.val 0 : K)*((dens i).getD j.val 0 : K) := by
    simpa only [Int.cast_mul] using congrArg (fun z : Int => (z : K))
      (rowNormalization_sound (D i) (nums i) (dens i) (B i) (hc i) j.val)
  apply mul_left_cancel₀ (hD i)
  rw [←mul_assoc,mul_inv_cancel₀ (hD i),one_mul,←mul_div_assoc]
  exact (div_eq_iff (hd i j)).mpr hi

def exceptionInteger {m n : Nat} (basis : Int) (D : Fin m → Int)
    (den : Fin m → Fin n → Int) : Int := basis*(∏ i,D i)*(∏ i,∏ j,den i j)

theorem exception_units {m n : Nat} (basis : Int) (D : Fin m → Int)
    (den : Fin m → Fin n → Int) (h : (exceptionInteger basis D den : K)≠0) :
    (basis : K)≠0 ∧ (∀ i, (D i : K)≠0) ∧ (∀ i j, (den i j : K)≠0) := by
  simpa only [exceptionInteger,Int.cast_mul,Int.cast_prod,mul_ne_zero_iff,
    Finset.prod_ne_zero_iff,Finset.mem_univ,forall_true_left,and_assoc] using h

#print axioms sourceRows_normalize
end CatalanCore.Uniform.Content

