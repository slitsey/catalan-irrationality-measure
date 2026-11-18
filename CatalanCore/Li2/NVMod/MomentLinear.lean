module
public import CatalanCore.Li2.NVMod.RationalMoments
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section
private def polylogLinear : ℚ[X]→ₗ[ℚ]RatFunc ℚ :=
  Polynomial.lsum (fun k=>{
    toFun := fun c=>(k:RatFunc ℚ)*algebraMap ℚ (RatFunc ℚ) c*liNeg (k-1) rfX
    map_add' := by intro c d;simp only [map_add,mul_add,add_mul]
    map_smul' := by
      intro c d
      simp only [RingHom.id_apply,smul_eq_mul,Algebra.smul_def,map_mul]
      ring})
private theorem polylogLinear_eq (P : ℚ[X]) :
    polylogLinear P=∑ k∈Icc 1 P.natDegree,
      (k:RatFunc ℚ)*algebraMap ℚ (RatFunc ℚ) (P.coeff k)*liNeg (k-1) rfX := by
  classical
  change P.sum (fun k c=>(k:RatFunc ℚ)*algebraMap ℚ (RatFunc ℚ) c*liNeg (k-1) rfX)=_
  rw [Polynomial.sum_over_range _ (by intro k;simp)]
  have hs : range (P.natDegree+1)=insert 0 (Icc 1 P.natDegree) := by
    ext k
    simp only [mem_range,mem_insert,mem_Icc]
    omega
  rw [hs,Finset.sum_insert (by simp)]
  simp
private theorem momentRF_eq_linear_formula (A : TypeKey) (g : ℚ[X]) :
    momentRF A g=
      (∑ m∈poleSet A,algebraMap ℚ (RatFunc ℚ) (residue A m*g.eval (-(m:ℚ)))*omegaRF m)+
        polylogLinear (polyPart A g) := by
  rw [polylogLinear_eq]
  exact momentRF_partial_fractions A g
theorem momentRF_add (A : TypeKey) (g h : ℚ[X]) :
    momentRF A (g+h)=momentRF A g+momentRF A h := by
  simp only [momentRF_eq_linear_formula,polyPart,mul_add,Polynomial.add_divByMonic,
    map_add,eval_add,Finset.sum_add_distrib,add_mul]
  ring
theorem momentRF_smul (A : TypeKey) (c : ℚ) (g : ℚ[X]) :
    momentRF A (c • g)=c • momentRF A g := by
  have hp : polyPart A (c • g)=c • polyPart A g := by
    simp only [polyPart,mul_smul_comm,Polynomial.smul_divByMonic]
  rw [momentRF_eq_linear_formula A (c • g),hp,momentRF_eq_linear_formula A g]
  simp only [map_smul,Polynomial.eval_smul,RingHom.id_apply]
  simp only [Algebra.smul_def]
  rw [mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [map_mul,Algebra.algebraMap_self_apply]
  ring
def momentRFLinear (A : TypeKey) : ℚ[X]→ₗ[ℚ]RatFunc ℚ where
  toFun := momentRF A
  map_add' := momentRF_add A
  map_smul' := momentRF_smul A
#print axioms momentRF_add
#print axioms momentRF_smul
end
end CatalanCore.Li2.NVMod
