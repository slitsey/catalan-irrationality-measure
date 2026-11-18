module
public import CatalanCore.Li2.NVMod.HermiteBlocks
public import CatalanCore.Li2.NVMod.AtZero
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

def infBasis (A : TypeKey) (i : ℕ) : ℚ[X] :=
  if A.kind=.U then if i=0 then 1 else hermitePoly A [] (poleList A) (i-1)
  else hermitePoly A [] (poleList A) i
def infLabel (A : TypeKey) (i : ℕ) : ℕ := (slots A).getD i 0
def infMatrix (A : TypeKey) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j=>(atInf (momentRF A (infBasis A i.val*infBasis A j.val))).coeff (infLabel A i.val:ℤ)

theorem infBasis_monic (A : TypeKey) (i : ℕ) : (infBasis A i).Monic := by
  unfold infBasis
  split_ifs
  · exact Polynomial.monic_one
  · exact hermitePoly_monic _ _ _ _
  · exact hermitePoly_monic _ _ _ _

theorem infBasis_degree (A : TypeKey) (i : ℕ) : (infBasis A i).natDegree=i := by
  unfold infBasis
  by_cases hU : A.kind=.U
  · rw [if_pos hU]
    by_cases hi : i=0
    · simp [hi]
    · rw [if_neg hi,hermitePoly_degree]
      simp only [hU,ite_true,List.length_nil,mul_zero,add_zero]
      omega
  · rw [if_neg hU,hermitePoly_degree]
    simp [hU]

theorem infLabel_U_zero (A : TypeKey) (hU : A.kind=.U) : infLabel A 0=0 := by
  simp [infLabel,slots,hU]
theorem infLabel_U_tail (A : TypeKey) (hU : A.kind=.U) (i : ℕ) :
    infLabel A (1+i)=nodeLabel (poleList A) i := by
  simp [infLabel,slots,hU,nodeLabel,poleSlots,List.getD,Nat.add_comm]
theorem infLabel_V (A : TypeKey) (hU : A.kind≠.U) (i : ℕ) :
    infLabel A i=nodeLabel (poleList A) i := by
  simp [infLabel,slots,hU,nodeLabel,poleSlots]

theorem infBasis_U_tail (A : TypeKey) (hU : A.kind=.U) (i : ℕ) :
    infBasis A (1+i)=hermitePoly A [] (poleList A) i := by simp [infBasis,hU]

theorem infBasis_moment_order (A : TypeKey) (i : ℕ) (h : ℚ[X])
    (hi : i<(slots A).length) :
    Oge (atInf (momentRF A (infBasis A i*h))) (infLabel A i:ℤ) := by
  by_cases hU : A.kind=.U
  · by_cases hz : i=0
    · subst i
      rw [infLabel_U_zero A hU]
      exact (moment_at_infinity A _).1
    · have hi' : i-1<3*(poleList A).length := by rw [slots_length] at hi; simp only [hU,ite_true] at hi; omega
      have he : i=1+(i-1) := by omega
      rw [he,infBasis_U_tail A hU,infLabel_U_tail A hU]
      exact hermite_moment_order A [] (poleList A) (i-1) h (by simp) hi'
  · rw [infLabel_V A hU]
    simp only [infBasis,if_neg hU]
    apply hermite_moment_order A [] (poleList A) i h (by simp)
    rw [slots_length] at hi
    simpa only [hU,ite_false,zero_add] using hi

theorem sum_getD_take (xs : List ℕ) (n : ℕ) (hn : n≤xs.length) :
    (∑ i : Fin n,(xs.getD i.val 0:ℤ))=((xs.take n).map (fun m=>(m:ℤ))).sum := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simp at hn
    | cons x xs =>
      rw [Fin.sum_univ_succ]
      change (x:ℤ)+(∑ i : Fin n,(xs.getD i.val 0:ℤ))=
        (x:ℤ)+((xs.take n).map (fun m=>(m:ℤ))).sum
      rw [ih xs (by simp only [List.length_cons] at hn; omega)]

theorem atInf_constant_basis (A : TypeKey) :
    atInf (constantRF A)=(Matrix.of fun i j : Fin A.size=>
      atInf (momentRF A (infBasis A i.val*infBasis A j.val))).det := by
  letI : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
  have hg := polynomial_gram_monic A.size (momentRFLinear A) (fun i=>infBasis A i.val)
    (fun i=>infBasis_monic A i.val) (fun i=>infBasis_degree A i.val)
  change (Matrix.of fun i j : Fin A.size=>momentRF A (infBasis A i.val*infBasis A j.val)).det=constantRF A at hg
  rw [←hg,atInf_eq_hom,RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact (atInf_eq_hom _).symm

theorem infMatrix_V (A : TypeKey) (n : ℕ) (hU : A.kind≠.U) :
    infMatrix A n=nodeMatrix A [] (poleList A) n := by
  apply Matrix.ext
  intro i j
  simp only [infMatrix,infBasis,if_neg hU,infLabel_V A hU,nodeMatrix]

theorem infMatrix_U_head (A : TypeKey) (hU : A.kind=.U) :
    (infMatrix A 1).det= -rfEval (rfDeriv (weight A)) 0 := by
  rw [Matrix.det_fin_one]
  change (atInf (momentRF A (infBasis A 0*infBasis A 0))).coeff (infLabel A 0:ℤ)=_
  have hB : infBasis A 0=1 := by simp [infBasis,hU]
  rw [hB,one_mul,infLabel_U_zero A hU]
  have hz : 0∉poleSet A := by simp [poleSet,hU]
  have hh := (moment_at_infinity A 1).2 0
  simpa [hz,rfPoly] using hh

theorem infMatrix_det_U_step (A : TypeKey) (n : ℕ) (hU : A.kind=.U)
    (hn : n≤3*(poleList A).length) :
    (infMatrix A (1+n)).det=
      -rfEval (rfDeriv (weight A)) 0*(nodeMatrix A [] (poleList A) n).det := by
  let M := infMatrix A (1+n)
  let C : Matrix (Fin n) (Fin 1) ℚ := fun i j=>M (Fin.natAdd 1 i) (Fin.castAdd n j)
  have he : M.submatrix finSumFinEquiv finSumFinEquiv=
      Matrix.fromBlocks (infMatrix A 1) 0 C (nodeMatrix A [] (poleList A) n) := by
    apply Matrix.ext
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j =>
        have hi : i.val=0 := by omega
        change (atInf (momentRF A (infBasis A i.val*infBasis A (1+j.val)))).coeff (infLabel A i.val:ℤ)=0
        rw [hi,infLabel_U_zero A hU,infBasis_U_tail A hU,mul_comm]
        have hord := hermite_moment_order A [] (poleList A) j.val (infBasis A 0) (by simp)
          (lt_of_lt_of_le j.isLt hn)
        have hmem := nodeLabel_mem (poleList A) j.val (lt_of_lt_of_le j.isLt hn)
        have hpos := poleList_U_pos A hU _ hmem
        exact hord 0 (by exact_mod_cast (show 0<nodeLabel (poleList A) j.val by omega))
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j =>
        change (atInf (momentRF A (infBasis A (1+i.val)*infBasis A (1+j.val)))).coeff
          (infLabel A (1+i.val):ℤ)=_
        rw [infBasis_U_tail A hU,infBasis_U_tail A hU,infLabel_U_tail A hU]
        rfl
  rw [←Matrix.det_submatrix_equiv_self finSumFinEquiv M,he,Matrix.det_fromBlocks_zero₁₂,
    infMatrix_U_head A hU]

theorem infMatrix_det_lead (A : TypeKey) (hs : A.size≤(slots A).length) :
    (infMatrix A A.size).det=infLead A := by
  by_cases hs0 : A.size=0
  · simp [hs0,infLead]
  rw [infLead,if_neg hs0]
  by_cases hU : A.kind=.U
  · rw [if_pos hU]
    have hn : A.size-1≤3*(poleList A).length := by
      rw [slots_length] at hs
      simp only [hU,ite_true] at hs
      omega
    have he : 1+(A.size-1)=A.size := by omega
    have hd := infMatrix_det_U_step A (A.size-1) hU hn
    rw [he] at hd
    rw [hd,nodeMatrix_det_fold A [] (poleList A) (A.size-1) (by simp) hn]
  · rw [if_neg hU,infMatrix_V A A.size hU]
    apply nodeMatrix_det_fold A [] (poleList A) A.size (by simp)
    rw [slots_length] at hs
    simpa only [hU,ite_false,zero_add] using hs

theorem hankel_at_infinity (A : TypeKey) (hs : A.size≤(slots A).length) :
    Oge (atInf (constantRF A)) (infOrder A) ∧
      (atInf (constantRF A)).coeff (infOrder A)=infLead A := by
  let M : Matrix (Fin A.size) (Fin A.size) (HahnSeries ℤ ℚ) := fun i j=>
    atInf (momentRF A (infBasis A i.val*infBasis A j.val))
  have hdet : M.det=atInf (constantRF A) := (atInf_constant_basis A).symm
  have hb := CatalanCore.Linalg.det_potential_coeff M (fun i=>(infLabel A i.val:ℤ)) (fun _=>0)
    (fun i j e he=>infBasis_moment_order A i.val (infBasis A j.val) (lt_of_lt_of_le i.isLt hs) e
      (by simpa only [add_zero] using he))
  simp only [Finset.sum_const_zero,add_zero] at hb
  have hsum : (∑ i : Fin A.size,(infLabel A i.val:ℤ))=infOrder A := sum_getD_take (slots A) A.size hs
  rw [hsum,hdet] at hb
  refine ⟨hb.1,?_⟩
  rw [hb.2]
  exact infMatrix_det_lead A hs

#print axioms infBasis_moment_order
#print axioms sum_getD_take
#print axioms atInf_constant_basis
#print axioms infMatrix_U_head
#print axioms infMatrix_det_U_step
#print axioms hankel_at_infinity
end
end CatalanCore.Li2.NVMod
