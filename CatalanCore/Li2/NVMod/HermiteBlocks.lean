module
public import CatalanCore.Li2.NVMod.HermiteBasis
public import CatalanCore.Li2.NVMod.InfinityOrder
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

theorem hermite_moment_order (A : TypeKey) (es ts : List ℕ) (i : ℕ) (h : ℚ[X])
    (hp : es++ts=poleList A) (hi : i<3*ts.length) :
    Oge (atInf (momentRF A (hermitePoly A es ts i*h))) (nodeLabel ts i:ℤ) := by
  apply moment_prefix_order
  · apply (mem_poleList A _).mp
    rw [←hp]
    exact List.mem_append_right _ (nodeLabel_mem ts i hi)
  · intro u hu hui
    exact dvd_mul_of_dvd_left (hermitePoly_previous_dvd A es ts i u hp hi hu hui) _
  · intro hU
    exact dvd_mul_of_dvd_left (hermitePoly_X_dvd A es ts i hU) _

theorem earlierPoly_eval_previous (A : TypeKey) (es ts : List ℕ) (t m : ℕ)
    (hp : es++t::ts=poleList A) (hm : m∈poleSet A) (hmt : m<t) :
    (earlierPoly A es).eval (-(m:ℚ))=0 := by
  obtain ⟨R,hR⟩ := earlierPoly_dvd A es m (prefix_pole_before A es ts t m hp hm hmt)
  rw [hR]
  simp [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add]

theorem hermite_head_coefficient (A : TypeKey) (es ts : List ℕ) (t i j : ℕ)
    (hp : es++t::ts=poleList A) (hi : i<3) (hj : j<3) :
    let Q := earlierPoly A es
    let Φ := (rfX+rfPoly (C (t:ℚ)))*(rfPoly Q)^2*weight A
    (atInf (momentRF A ((Q*(X+C (t:ℚ))^i)*(Q*(X+C (t:ℚ))^j)))).coeff (t:ℤ)=
      jetScalar (rfEval Φ (-(t:ℚ))) (rfEval (rfDeriv Φ) (-(t:ℚ)))
        (rfEval (rfDeriv (rfDeriv Φ)) (-(t:ℚ))) (i+j) := by
  dsimp only
  let Q := earlierPoly A es
  let Φ := (rfX+rfPoly (C (t:ℚ)))*(rfPoly Q)^2*weight A
  have ht : t∈poleSet A := (mem_poleList A t).mp (by rw [←hp]; simp)
  rw [(moment_at_infinity A _).2 t]
  have hs : (∑ m∈(poleSet A).filter (fun m=>m<t),
      residue A m*((Q*(X+C (t:ℚ))^i)*(Q*(X+C (t:ℚ))^j)).eval (-(m:ℚ))/((m:ℚ)-t)^2)=0 := by
    apply Finset.sum_eq_zero
    intro m hm
    obtain ⟨hm,hmt⟩ := Finset.mem_filter.mp hm
    have hz : Q.eval (-(m:ℚ))=0 := earlierPoly_eval_previous A es ts t m hp hm hmt
    simp only [Polynomial.eval_mul,hz,zero_mul,mul_zero,zero_div]
  change -(∑ m∈(poleSet A).filter (fun m=>m<t),
    residue A m*((Q*(X+C (t:ℚ))^i)*(Q*(X+C (t:ℚ))^j)).eval (-(m:ℚ))/((m:ℚ)-t)^2)-
      (if t∈poleSet A then _ else _)=_
  rw [hs,if_pos ht,neg_zero,zero_sub]
  have he : (rfX+rfPoly (C (t:ℚ)))*
      rfPoly ((Q*(X+C (t:ℚ))^i)*(Q*(X+C (t:ℚ))^j))*weight A=
      Φ*rfPoly ((X+C (t:ℚ))^(i+j)) := by
    dsimp only [Φ]
    simp only [rfPoly,map_mul,map_pow,pow_add]
    ring
  rw [he]
  simpa only [neg_div] using second_product_linear_power Φ t (i+j) (polePhi_regular A Q t ht) (by omega)

theorem earlierPoly_eval_current_ne (A : TypeKey) (es ts : List ℕ) (t : ℕ)
    (hp : es++t::ts=poleList A) : (earlierPoly A es).eval (-(t:ℚ))≠0 := by
  apply earlierPoly_eval_ne_zero
  · have hn : (es++t::ts).Nodup := hp ▸ poleList_nodup A
    exact fun ht=>(List.nodup_append.mp hn).2.2 t ht t (by simp) rfl
  · intro hU
    have ht : t∈poleList A := by rw [←hp]; simp
    have hpos := poleList_U_pos A hU t ht
    omega

def nodeMatrix (A : TypeKey) (es ts : List ℕ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j=>(atInf (momentRF A (hermitePoly A es ts i.val*hermitePoly A es ts j.val))).coeff
    (nodeLabel ts i.val:ℤ)

theorem nodeMatrix_head (A : TypeKey) (es ts : List ℕ) (t n : ℕ)
    (hp : es++t::ts=poleList A) (hn : n≤3) :
    let Q := earlierPoly A es
    let Φ := (rfX+rfPoly (C (t:ℚ)))*(rfPoly Q)^2*weight A
    nodeMatrix A es (t::ts) n=jetBlock n (rfEval Φ (-(t:ℚ)))
      (rfEval (rfDeriv Φ) (-(t:ℚ))) (rfEval (rfDeriv (rfDeriv Φ)) (-(t:ℚ))) := by
  dsimp only
  apply Matrix.ext
  intro i j
  have hi : i.val<3 := lt_of_lt_of_le i.isLt hn
  have hj : j.val<3 := lt_of_lt_of_le j.isLt hn
  simp only [nodeMatrix,hermitePoly,nodeLabel_cons,if_pos hi,if_pos hj,jetBlock]
  exact hermite_head_coefficient A es ts t i.val j.val hp hi hj

theorem hermitePoly_tail (A : TypeKey) (es ts : List ℕ) (t i : ℕ) :
    hermitePoly A es (t::ts) (3+i)=hermitePoly A (es++[t]) ts i := by
  simp [hermitePoly]

theorem nodeLabel_tail (ts : List ℕ) (t i : ℕ) :
    nodeLabel (t::ts) (3+i)=nodeLabel ts i := by
  simp [nodeLabel_cons]

theorem nodeMatrix_upper_zero (A : TypeKey) (es ts : List ℕ) (t n : ℕ)
    (hp : es++t::ts=poleList A) (hn : n≤3*ts.length)
    (i : Fin 3) (j : Fin n) :
    nodeMatrix A es (t::ts) (3+n) (Fin.castAdd n i) (Fin.natAdd 3 j)=0 := by
  have hi : i.val<3 := i.isLt
  change (atInf (momentRF A (hermitePoly A es (t::ts) i.val*
    hermitePoly A es (t::ts) (3+j.val)))).coeff (nodeLabel (t::ts) i.val:ℤ)=0
  rw [nodeLabel_cons,if_pos hi,hermitePoly_tail,mul_comm]
  have hprefix : (es++[t])++ts=poleList A := by simpa only [List.append_assoc,List.singleton_append] using hp
  have hord := hermite_moment_order A (es++[t]) ts j.val (hermitePoly A es (t::ts) i.val)
    hprefix (lt_of_lt_of_le j.isLt hn)
  have hm : nodeLabel ts j.val∈ts := nodeLabel_mem ts j.val (lt_of_lt_of_le j.isLt hn)
  have hpair : (es++t::ts).Pairwise (·<·) := hp ▸ poleList_pairwise A
  have hgt := (List.pairwise_cons.mp (List.pairwise_append.mp hpair).2.1).1 _ hm
  exact hord (t:ℤ) (by exact_mod_cast hgt)

theorem nodeMatrix_tail (A : TypeKey) (es ts : List ℕ) (t n : ℕ) (i j : Fin n) :
    nodeMatrix A es (t::ts) (3+n) (Fin.natAdd 3 i) (Fin.natAdd 3 j)=
      nodeMatrix A (es++[t]) ts n i j := by
  change (atInf (momentRF A (hermitePoly A es (t::ts) (3+i.val)*
    hermitePoly A es (t::ts) (3+j.val)))).coeff (nodeLabel (t::ts) (3+i.val):ℤ)=_
  rw [hermitePoly_tail,hermitePoly_tail,nodeLabel_tail]
  rfl

theorem nodeMatrix_det_step (A : TypeKey) (es ts : List ℕ) (t n : ℕ)
    (hp : es++t::ts=poleList A) (hn : n≤3*ts.length) :
    (nodeMatrix A es (t::ts) (3+n)).det=
      (nodeMatrix A es (t::ts) 3).det*(nodeMatrix A (es++[t]) ts n).det := by
  let M := nodeMatrix A es (t::ts) (3+n)
  let C : Matrix (Fin n) (Fin 3) ℚ := fun i j=>M (Fin.natAdd 3 i) (Fin.castAdd n j)
  have he : M.submatrix finSumFinEquiv finSumFinEquiv=
      Matrix.fromBlocks (nodeMatrix A es (t::ts) 3) 0 C (nodeMatrix A (es++[t]) ts n) := by
    apply Matrix.ext
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => exact nodeMatrix_upper_zero A es ts t n hp hn i j
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j => exact nodeMatrix_tail A es ts t n i j
  rw [←Matrix.det_submatrix_equiv_self finSumFinEquiv M,he,Matrix.det_fromBlocks_zero₁₂]

theorem nodeMatrix_det_fold (A : TypeKey) (es ts : List ℕ) (n : ℕ)
    (hp : es++ts=poleList A) (hn : n≤3*ts.length) :
    (nodeMatrix A es ts n).det=infFold A ts n es := by
  induction ts generalizing es n with
  | nil =>
    have hn0 : n=0 := by simp only [List.length_nil,mul_zero] at hn; omega
    subst n
    simp [infFold]
  | cons t ts ih =>
    by_cases hn0 : n=0
    · subst n; simp [infFold]
    have ht : t∈poleSet A := (mem_poleList A t).mp (by rw [←hp]; simp)
    let Q := earlierPoly A es
    let Φ := (rfX+rfPoly (C (t:ℚ)))*(rfPoly Q)^2*weight A
    have hreg : RFRegular (-(t:ℚ)) Φ := polePhi_regular A Q t ht
    have hphi : rfEval Φ (-(t:ℚ))=residue A t*(Q.eval (-(t:ℚ)))^2 := polePhi_eval A Q t ht
    have hne : rfEval Φ (-(t:ℚ))≠0 := by
      rw [hphi]
      exact mul_ne_zero (residue_ne_zero A t ht) (pow_ne_zero _ (earlierPoly_eval_current_ne A es ts t hp))
    by_cases h3 : 3≤n
    · have hn' : n-3≤3*ts.length := by simp only [List.length_cons] at hn; omega
      have he : 3+(n-3)=n := by omega
      have hstep := nodeMatrix_det_step A es ts t (n-3) hp hn'
      rw [he] at hstep
      rw [hstep,nodeMatrix_head A es ts t 3 hp (by omega),jet_det_three]
      have hp' : (es++[t])++ts=poleList A := by simpa only [List.append_assoc,List.singleton_append] using hp
      rw [ih (es++[t]) (n-3) hp' hn']
      rw [infFold,if_neg hn0,if_pos h3]
      change (rfEval Φ (-(t:ℚ)))^3*infFold A ts (n-3) (es++[t])=_
      rw [hphi]
      dsimp only [Q]
      ring
    · rw [infFold,if_neg hn0,if_neg h3,nodeMatrix_head A es ts t n hp (by omega)]
      have hj := jet_det_logarithmic Φ (-(t:ℚ)) hreg hne
      dsimp only at hj
      have hsmall : n=1∨n=2 := by omega
      rcases hsmall with rfl|rfl
      · simpa only [partialInf,ite_true] using hj.1
      · simpa only [partialInf,show ¬(2:ℕ)=1 by omega,ite_false] using hj.2

#print axioms nodeMatrix_head
#print axioms nodeMatrix_det_step
#print axioms nodeMatrix_det_fold
end
end CatalanCore.Li2.NVMod

