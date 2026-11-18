module
public import CatalanCore.Li2.NVMod.Definitions
public import CatalanCore.Basic.PrimePower
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NV
open NVMod
noncomputable section

private def poleProduct {R : Type*} [CommRing R] (S : Finset ℕ) : R[X] :=
  ∏ m∈S, (X+C (m:R))

private theorem poleProduct_monic {R : Type*} [CommRing R] [Nontrivial R] (S : Finset ℕ) :
    (poleProduct (R:=R) S).Monic :=
  monic_prod_of_monic _ _ (fun m _ => monic_X_add_C _)

private theorem rational_decomposition (A : ℚ[X]) (S : Finset ℕ) :
    A=(A /ₘ poleProduct S)*poleProduct S+
      ∑ m∈S, C (A.eval (-(m:ℚ))/∏ n∈S.erase m,((n:ℚ)-m))*poleProduct (S.erase m) := by
  classical
  have hinj : Set.InjOn (fun m : ℕ => -(m:ℚ)) S := by
    intro m hm n hn h
    exact_mod_cast (neg_injective h)
  have hdeg : (poleProduct (R:=ℚ) S).natDegree=S.card := by
    unfold poleProduct
    rw [natDegree_prod_of_monic _ _ (fun m _ => monic_X_add_C _)]
    simp only [natDegree_X_add_C,Finset.sum_const,smul_eq_mul,mul_one]
  have hmod : A %ₘ poleProduct S =
      ∑ m∈S, C (A.eval (-(m:ℚ))/∏ n∈S.erase m,((n:ℚ)-m))*poleProduct (S.erase m) := by
    rw [Lagrange.eq_interpolate_of_eval_eq (f:=A %ₘ poleProduct S)
      (fun m : ℕ => A.eval (-(m:ℚ))) hinj
      (by have h:=degree_modByMonic_lt A (poleProduct_monic (R:=ℚ) S)
          rwa [degree_eq_natDegree (poleProduct_monic (R:=ℚ) S).ne_zero,hdeg] at h)
      (by
        intro m hm
        have h1:=modByMonic_add_div A (poleProduct S)
        have hz : (poleProduct (R:=ℚ) S).eval (-(m:ℚ))=0 := by
          simp only [poleProduct,eval_prod,eval_add,eval_X,eval_C]
          exact Finset.prod_eq_zero hm (by simp)
        conv_rhs => rw [← h1]
        simp only [eval_add,eval_mul,hz,zero_mul,add_zero])]
    simp only [Lagrange.interpolate_apply]
    apply Finset.sum_congr rfl
    intro m hm
    unfold Lagrange.basis Lagrange.basisDivisor poleProduct
    simp only [neg_sub_neg,sub_neg_eq_add,Finset.prod_mul_distrib,← map_prod,
      Finset.prod_inv_distrib,div_eq_mul_inv,C_mul,mul_assoc, map_neg,sub_neg_eq_add]
    simp only [add_comm (-(m:ℚ)), ← sub_eq_add_neg]

  calc
    A = A %ₘ poleProduct S + poleProduct S*(A /ₘ poleProduct S) := (modByMonic_add_div A (poleProduct S)).symm
    _ = _ := by rw [hmod]; ring

/-- Integral partial fractions at pairwise unit-separated integer poles. -/
theorem integral_partial_fractions (ℓ : ℕ) [Fact ℓ.Prime]
    (P : (Basic.LocRing ℓ)[X]) (S : Finset ℕ)
    (hsep : ∀ m∈S, ∀ n∈S, m≠n → IsUnit ((m:Basic.LocRing ℓ)-n)) :
  ∃ (Q : (Basic.LocRing ℓ)[X]) (ρ : ℕ→Basic.LocRing ℓ),
    rfPoly (P.map (Basic.LocRing ℓ).subtype) /
      ∏ m∈S, (rfX+rfPoly (C (m:ℚ))) =
    rfPoly (Q.map (Basic.LocRing ℓ).subtype) +
      ∑ m∈S, rfPoly (C (ρ m:ℚ))/(rfX+rfPoly (C (m:ℚ))) := by
  classical
  let R := Basic.LocRing ℓ
  let f : R →+* ℚ := R.subtype
  let D : R[X] := poleProduct S
  let den (m : ℕ) : R := ∏ n∈S.erase m, ((n:R)-m)
  have hex : ∀ m, ∃ v:R, m∈S → den m*v=1 := by
    intro m
    by_cases hm : m∈S
    · have hu : IsUnit (den m) := by
        dsimp only [den]
        apply Finset.prod_induction (fun (n : ℕ) => ((n:R)-m)) IsUnit
          (fun a b ha hb => ha.mul hb) isUnit_one
        intro n hn
        exact hsep n (Finset.mem_of_mem_erase hn) m hm (Finset.ne_of_mem_erase hn)
      obtain ⟨v,hv⟩:=hu.exists_right_inv
      exact ⟨v,fun _ => hv⟩
    · exact ⟨0,fun h => False.elim (hm h)⟩
  choose v hv using hex
  let rho (m : ℕ) : R := P.eval (-(m:R))*v m
  have hmapD : D.map f=poleProduct (R:=ℚ) S := by
    unfold D poleProduct
    rw [Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro m hm
    simp only [Polynomial.map_add,Polynomial.map_X,Polynomial.map_C,Polynomial.map_natCast,map_natCast]
  have hmapQ : (P /ₘ D).map f=P.map f /ₘ poleProduct S := by
    rw [Polynomial.map_divByMonic f (poleProduct_monic S),hmapD]
  have hrho : ∀ m∈S, f (rho m)=
      (P.map f).eval (-(m:ℚ))/∏ n∈S.erase m,((n:ℚ)-m) := by
    intro m hm
    have hh:=congrArg f (hv m hm)
    have hn : (∏ n∈S.erase m,((n:ℚ)-m))*f (v m)=1 := by simpa [den] using hh
    have hne : (∏ n∈S.erase m,((n:ℚ)-m))≠0 := by intro h;rw [h,zero_mul] at hn;exact zero_ne_one hn
    have hvq : f (v m)=(∏ n∈S.erase m,((n:ℚ)-m))⁻¹ := by
      apply (mul_left_cancel₀ hne)
      rw [hn,mul_inv_cancel₀ hne]
    have heval : f (P.eval (-(m:R)))=(P.map f).eval (-(m:ℚ)) := by
      simpa only [map_neg,map_natCast] using (Polynomial.eval_map_apply (f:=f) (p:=P) (-(m:R))).symm
    simp only [rho,map_mul,heval,hvq,div_eq_mul_inv]
  refine ⟨P /ₘ D,rho,?_⟩
  let dq : ℚ[X] := poleProduct S
  have hpoly : P.map f=(P /ₘ D).map f*dq+
      ∑ m∈S, C (f (rho m))*poleProduct (S.erase m) := by
    rw [hmapQ]
    calc
      P.map f = (P.map f /ₘ poleProduct S)*poleProduct S+
        ∑ m∈S, C ((P.map f).eval (-(m:ℚ))/∏ n∈S.erase m,((n:ℚ)-m))*poleProduct (S.erase m) := rational_decomposition (P.map f) S
      _ = _ := by
        apply congrArg₂ (·+·) rfl
        exact Finset.sum_congr rfl (fun m hm => by rw [hrho m hm])
  have hline : ∀ m : ℕ, rfPoly (X+C (m:ℚ))≠(0:RatFunc ℚ) := by
    intro m
    exact RatFunc.algebraMap_ne_zero (monic_X_add_C (m:ℚ)).ne_zero
  have hd : rfPoly dq≠(0:RatFunc ℚ) := by
    simp only [dq,poleProduct,rfPoly,map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun m hm => hline m)
  have hprod : (∏ m∈S, (rfX+rfPoly (C (m:ℚ))))=rfPoly dq := by
    simp [dq,poleProduct,rfX,rfPoly]
  rw [hprod]
  apply (div_eq_iff hd).mpr
  rw [add_mul,Finset.sum_mul]
  have hp:=congrArg (algebraMap ℚ[X] (RatFunc ℚ)) hpoly
  simp only [map_add,map_mul,map_sum] at hp
  change rfPoly (P.map f) = _
  change rfPoly (P.map f) = _ at hp
  rw [hp]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hde : dq=(X+C (m:ℚ))*poleProduct (S.erase m) := by
    exact (Finset.mul_prod_erase S (fun m => X+C (m:ℚ)) hm).symm
  rw [hde]
  simp only [rfPoly,rfX,map_add,map_mul]
  have hn : (algebraMap ℚ[X] (RatFunc ℚ)) X + (algebraMap ℚ[X] (RatFunc ℚ)) (C (m:ℚ))≠0 := by
    simpa only [rfPoly,map_add] using hline m
  change _ = (algebraMap ℚ[X] (RatFunc ℚ)) (C (f (rho m))) / _ * _
  field_simp [hn]
  <;> ring

#print axioms integral_partial_fractions
end
end CatalanCore.Li2.NV
