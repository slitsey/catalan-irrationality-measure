module
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialSourceLists
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.DataSupport
noncomputable section

theorem range_sum {S : Type*} [AddCommMonoid S] (f : ℕ→S) (m : ℕ) :
    ((List.range m).map f).sum=∑ b∈range m,f b := by
  induction m with
  | zero=>simp
  | succ m ih=>simp [List.range_succ,List.map_append,Finset.sum_range_succ,ih]

def quotientCoefficients (qs : List ℚ) (order : ℕ) : List ℚ :=
  sumCoefficients ((List.range qs.length).map (fun (j : ℕ)=>
    coefficientsScale ((j:ℚ)*qs.getD j 0) (liCoefficients order (j-1))))

theorem quotientClearingPoly_sum (P : ℚ[X]) (order : ℕ) :
    quotientClearingPoly P order=P.sum (fun j c=>C ((j:ℚ)*c)*liNumerator order (j-1)) := by
  rw [Polynomial.sum_over_range _ (by intro j;simp)]
  have hs : range (P.natDegree+1)=insert 0 (Icc 1 P.natDegree) := by
    ext j
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
    omega
  rw [hs,Finset.sum_insert (by simp)]
  simp [quotientClearingPoly]

theorem quotientCoefficients_spec (qs : List ℚ) (order : ℕ) :
    coefficientsPoly (quotientCoefficients qs order)=quotientClearingPoly (coefficientsPoly qs) order := by
  cases qs with
  | nil=>simp [quotientCoefficients,sumCoefficients,coefficientsPoly,quotientClearingPoly]
  | cons a as=>
    have hd : (coefficientsPoly (a::as)).natDegree<(a::as).length := by
      have hh : (coefficientsPoly (a::as)).natDegree≤as.length := by
        apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro j hj
        rw [coefficientsPoly_coeff]
        exact List.getD_eq_default _ _ (by simp only [List.length_cons];omega)
      exact Nat.lt_succ_of_le hh
    rw [quotientClearingPoly_sum,Polynomial.sum_over_range' _ (by intro j;simp) _ hd]
    simp only [quotientCoefficients,sumCoefficients_spec,List.map_map,Function.comp_def,
      coefficientsPoly_scale,liCoefficients_spec,coefficientsPoly_coeff]
    exact range_sum (fun j : ℕ=>C ((j:ℚ)*(a::as).getD j 0)*liNumerator order (j-1)) _

def poleCoefficients (ms : List ℕ) (rho : ℕ→ℚ) (e cutoff : ℕ) : List ℚ :=
  sumCoefficients (ms.map (fun m=>coefficientsScale (rho m*(-(m:ℚ))^e) (omegaCoefficients cutoff m)))

theorem poleCoefficients_spec (ms : List ℕ) (hn : ms.Nodup) (rho : ℕ→ℚ) (e cutoff : ℕ) :
    coefficientsPoly (poleCoefficients ms rho e cutoff)=poleClearingPoly ms.toFinset rho e cutoff := by
  simp only [poleCoefficients,sumCoefficients_spec,List.map_map,Function.comp_def,
    coefficientsPoly_scale,omegaCoefficients_spec]
  rw [←List.sum_toFinset (fun m=>C (rho m*(-(m:ℚ))^e)*omegaNumerator cutoff m) hn]
  rfl

def clearedCoefficients (ms : List ℕ) (rho : ℕ→ℚ) (qs : List ℚ)
    (e D cutoff order : ℕ) : List ℚ :=
  coefficientsScale (D:ℚ) (coefficientsAdd
    (coefficientsMul (powerCoefficients order [1,-1]) (poleCoefficients ms rho e cutoff))
    (coefficientsMul (monomialCoefficients cutoff 1) (quotientCoefficients qs order)))

theorem clearedCoefficients_spec (ms : List ℕ) (hn : ms.Nodup) (rho : ℕ→ℚ) (qs : List ℚ)
    (e D cutoff order : ℕ) :
    coefficientsPoly (clearedCoefficients ms rho qs e D cutoff order)=
      clearedSourcePoly ms.toFinset rho (coefficientsPoly qs) e D cutoff order := by
  simp only [clearedCoefficients,coefficientsPoly_scale,coefficientsPoly_add,coefficientsPoly_mul,
    powerCoefficients_spec,poleCoefficients_spec ms hn,monomialCoefficients_spec,
    quotientCoefficients_spec]
  rw [show coefficientsPoly ([1,-1]:List ℚ)=(1-X:ℚ[X]) by
    simp [coefficientsPoly]
    ring]
  simp only [map_one,one_mul]
  rfl
#print axioms clearedCoefficients_spec
end
end CatalanCore.Li2.NVMod.DataSupport
