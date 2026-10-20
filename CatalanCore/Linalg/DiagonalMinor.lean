module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic

@[expose] public section
open Finset Matrix
namespace CatalanCore.Linalg
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

def identityRows (M : Matrix ι ι R) (t : Finset ι) : Matrix ι ι R :=
  fun i j=>if i∈t then if i=j then 1 else 0 else M i j

lemma identityRows_insert_det (M : Matrix ι ι R) (t : Finset ι) (i : ι) (hi : i∉t) :
    (identityRows (M+Matrix.diagonal (Pi.single i 1)) t).det=
      (identityRows M t).det+(identityRows M (insert i t)).det := by
  have hm : identityRows (M+Matrix.diagonal (Pi.single i 1)) t=
      (identityRows M t).updateRow i ((identityRows M t) i+Pi.single i 1) := by
    ext a b
    simp only [Matrix.updateRow_apply]
    by_cases ha : a=i
    · subst a;simp [identityRows,hi,Matrix.updateRow_apply,Matrix.diagonal_apply,Pi.single_apply, eq_comm]
    · by_cases hab : a=b
      · subst b; simp [identityRows,ha,Ne.symm ha,Matrix.diagonal_apply,Pi.single_apply]
      · simp [identityRows,ha,Ne.symm ha,hab,Ne.symm hab,Matrix.diagonal_apply,Pi.single_apply]
  have hu : (identityRows M t).updateRow i (Pi.single i 1)=identityRows M (insert i t) := by
    ext a b
    simp only [Matrix.updateRow_apply]
    by_cases ha : a=i
    · subst a;simp [identityRows,Matrix.updateRow_apply,Pi.single_apply, eq_comm]
    · simp [identityRows,ha,Matrix.updateRow_apply]
  rw [hm,Matrix.det_updateRow_add,Matrix.updateRow_eq_self,hu]

lemma identityRows_compl_det (M : Matrix ι ι R) (s : Finset ι) :
    (identityRows M sᶜ).det=(M.submatrix (Subtype.val : s→ι) Subtype.val).det := by
  let e : s⊕{i : ι//i∉s}≃ι:=Equiv.sumCompl (fun i=>i∈s)
  let B : Matrix s {i : ι//i∉s} R:=fun i j=>M i j
  have hm : (identityRows M sᶜ).submatrix e e=
      Matrix.fromBlocks (M.submatrix (Subtype.val : s→ι) Subtype.val) B 0 1 := by
    ext a b
    rcases a with a|a <;> rcases b with b|b
    · simp [e,identityRows,Equiv.sumCompl_apply_inl,a.property,Matrix.fromBlocks]
    · simp [e,identityRows,Equiv.sumCompl_apply_inl,Equiv.sumCompl_apply_inr,a.property,Matrix.fromBlocks,B]
    · have hab : a.val≠b.val:=fun h=>a.property (h ▸ b.property)
      simp [e,identityRows,Equiv.sumCompl_apply_inl,Equiv.sumCompl_apply_inr,a.property,Matrix.fromBlocks,hab]
    · simp [e,identityRows,Equiv.sumCompl_apply_inr,a.property,Matrix.fromBlocks,Matrix.one_apply,Subtype.ext_iff] <;> rfl
  have hd:=Matrix.det_submatrix_equiv_self e (identityRows M sᶜ)
  rw [hm,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one] at hd
  exact hd.symm

/-- Diagonal perturbation stability transfers any additive determinant bound
to every principal restriction. Only integral perturbations are required. -/
theorem principal_mem_of_diagonal_stability (O : Subring R) (J : AddSubgroup R)
    (M : Matrix ι ι R) (s : Finset ι)
    (h : ∀d : ι→O,(∀i∈s,d i=0)→
      (M+Matrix.diagonal (fun i=>(d i:R))).det∈J) :
    (M.submatrix (Subtype.val : s→ι) Subtype.val).det∈J := by
  have hempty (A : Matrix ι ι R) : identityRows A ∅ = A := by ext a b; simp [identityRows]
  have H (t : Finset ι) (ht : t⊆sᶜ) : ∀d : ι→O,(∀i∈s,d i=0)→
      (identityRows (M+Matrix.diagonal (fun i=>(d i:R))) t).det∈J := by
    induction t using Finset.induction_on with
    | empty =>intro d hd;simpa only [hempty] using h d hd
    | @insert i t hi ih =>
      intro d hd
      have hiS : i∉s:=Finset.mem_compl.mp (ht (mem_insert_self _ _))
      have htS : t⊆sᶜ:=fun j hj=>ht (mem_insert_of_mem hj)
      let d' : ι→O:=fun j=>d j+if j=i then 1 else 0
      have hd' : ∀j∈s,d' j=0 := by
        intro j hj
        have hji : j≠i:=fun he=>hiS (he ▸ hj)
        simp [d',hji,hd j hj]
      have hplus:=ih htS d' hd'
      have hbase:=ih htS d hd
      have he : M+Matrix.diagonal (fun j=>(d' j:R))=
          (M+Matrix.diagonal (fun j=>(d j:R)))+Matrix.diagonal (Pi.single i 1) := by
        ext a b
        by_cases hab : a=b
        · subst b;by_cases hai : a=i <;> simp [d',Matrix.diagonal_apply,Pi.single_apply,hai,add_assoc]
        · simp [Matrix.diagonal_apply,hab]
      rw [he,identityRows_insert_det _ _ _ hi] at hplus
      have hh:=J.sub_mem hplus hbase
      simpa only [add_sub_cancel_left] using hh
  have hh:=H sᶜ (Finset.Subset.refl _) (fun _=>0) (by simp)
  simpa only [Subring.coe_zero,Matrix.diagonal_zero,add_zero,identityRows_compl_det] using hh
end CatalanCore.Linalg
