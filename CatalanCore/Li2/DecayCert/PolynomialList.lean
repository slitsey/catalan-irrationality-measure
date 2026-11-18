module
public import CatalanCore.Li2.DecayCert.RealCells
public import CatalanCore.Uniform.Decay.Tools.BernsteinList
@[expose] public section
set_option Elab.async false
open Polynomial Set
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert

def qListAdd (a b : List ℚ) : List ℚ :=
  (List.range (max a.length b.length)).map (fun j : ℕ => coeffQ a j+coeffQ b j)
def qListScale (c : ℚ) (a : List ℚ) : List ℚ := a.map (fun q : ℚ => c*q)
def qListSub (a b : List ℚ) : List ℚ := qListAdd a (qListScale (-1) b)
def qListShift (a : List ℚ) : List ℚ := 0::a
noncomputable def qListPoly (a : List ℚ) : ℚ[X] :=
  ∑ j ∈ Finset.range a.length,C (coeffQ a j)*X^j

theorem qListPoly_coeff (a : List ℚ) (j : ℕ) : (qListPoly a).coeff j=coeffQ a j := by
  simp only [qListPoly,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  by_cases hj : j < a.length
  · simp [hj]
  · simp [hj,coeffQ_eq_zero_of_ge a j (by omega)]

theorem coeffQ_qListAdd (a b : List ℚ) (j : ℕ) :
    coeffQ (qListAdd a b) j=coeffQ a j+coeffQ b j := by
  by_cases hj : j < max a.length b.length
  · simp [qListAdd,coeffQ,List.getElem?_range hj]
  · have hj' : max a.length b.length ≤ j := by omega
    have ha : a.length ≤ j := (le_max_left a.length b.length).trans hj'
    have hb : b.length ≤ j := (le_max_right a.length b.length).trans hj'
    have hc : (qListAdd a b).length ≤ j := by simp [qListAdd]; omega
    rw [coeffQ_eq_zero_of_ge _ _ hc,coeffQ_eq_zero_of_ge a j ha,coeffQ_eq_zero_of_ge b j hb,add_zero]

theorem coeffQ_qListScale (c : ℚ) (a : List ℚ) (j : ℕ) :
    coeffQ (qListScale c a) j=c*coeffQ a j := by
  cases hh : a[j]? <;> simp [qListScale,coeffQ,hh]

theorem qListPoly_add (a b : List ℚ) : qListPoly (qListAdd a b)=qListPoly a+qListPoly b := by
  ext j
  rw [Polynomial.coeff_add,qListPoly_coeff,qListPoly_coeff,qListPoly_coeff,coeffQ_qListAdd]

theorem qListPoly_scale (c : ℚ) (a : List ℚ) : qListPoly (qListScale c a)=C c*qListPoly a := by
  ext j
  rw [Polynomial.coeff_C_mul,qListPoly_coeff,qListPoly_coeff,coeffQ_qListScale]

theorem qListPoly_sub (a b : List ℚ) : qListPoly (qListSub a b)=qListPoly a-qListPoly b := by
  rw [qListSub,qListPoly_add,qListPoly_scale]
  simp [sub_eq_add_neg]

theorem qListPoly_shift (a : List ℚ) : qListPoly (qListShift a)=X*qListPoly a := by
  ext j
  cases j with
  | zero => simp [qListPoly_coeff,qListShift,coeffQ]
  | succ j =>
    rw [Polynomial.coeff_X_mul,qListPoly_coeff,qListPoly_coeff]
    simp [qListShift,coeffQ]

def qChebPair (a₁ : ℚ) : ℕ → List ℚ×List ℚ
  | 0 => ([1],[0,a₁])
  | n+1 =>
    let p := qChebPair a₁ n
    (p.2,qListSub (qListScale 2 (qListShift p.2)) p.1)
def qChebT (n : ℕ) : List ℚ := (qChebPair 1 n).1
def qChebU (n : ℕ) : List ℚ := (qChebPair 2 n).1

theorem qChebT_pair_spec (n : ℕ) :
    qListPoly (qChebPair 1 n).1=Polynomial.Chebyshev.T ℚ (n:ℤ) ∧
      qListPoly (qChebPair 1 n).2=Polynomial.Chebyshev.T ℚ ((n:ℤ)+1) := by
  induction n with
  | zero => simp [qChebPair,qListPoly,coeffQ,Finset.sum_range_succ,Polynomial.C_ofNat]
  | succ n ih =>
    change qListPoly (qChebPair 1 n).2=Polynomial.Chebyshev.T ℚ ((n+1:ℕ):ℤ) ∧
      qListPoly (qListSub (qListScale 2 (qListShift (qChebPair 1 n).2)) (qChebPair 1 n).1)=
        Polynomial.Chebyshev.T ℚ (((n+1:ℕ):ℤ)+1)
    constructor
    · simpa only [Nat.cast_add,Nat.cast_one] using ih.2
    · rw [qListPoly_sub,qListPoly_scale,qListPoly_shift,ih.2,ih.1]
      have hC : (C (2:ℚ):ℚ[X])=2 := Polynomial.C_ofNat 2
      have hidx : ((n+1:ℕ):ℤ)+1=(n:ℤ)+2 := by omega
      rw [hC,hidx]
      simpa only [mul_assoc] using (Polynomial.Chebyshev.T_add_two ℚ (n:ℤ)).symm

theorem qChebU_pair_spec (n : ℕ) :
    qListPoly (qChebPair 2 n).1=Polynomial.Chebyshev.U ℚ (n:ℤ) ∧
      qListPoly (qChebPair 2 n).2=Polynomial.Chebyshev.U ℚ ((n:ℤ)+1) := by
  induction n with
  | zero => simp [qChebPair,qListPoly,coeffQ,Finset.sum_range_succ,Polynomial.C_ofNat]
  | succ n ih =>
    change qListPoly (qChebPair 2 n).2=Polynomial.Chebyshev.U ℚ ((n+1:ℕ):ℤ) ∧
      qListPoly (qListSub (qListScale 2 (qListShift (qChebPair 2 n).2)) (qChebPair 2 n).1)=
        Polynomial.Chebyshev.U ℚ (((n+1:ℕ):ℤ)+1)
    constructor
    · simpa only [Nat.cast_add,Nat.cast_one] using ih.2
    · rw [qListPoly_sub,qListPoly_scale,qListPoly_shift,ih.2,ih.1]
      have hC : (C (2:ℚ):ℚ[X])=2 := Polynomial.C_ofNat 2
      have hidx : ((n+1:ℕ):ℤ)+1=(n:ℤ)+2 := by omega
      rw [hC,hidx]
      simpa only [mul_assoc] using (Polynomial.Chebyshev.U_add_two ℚ (n:ℤ)).symm

theorem qChebT_spec (n : ℕ) : qListPoly (qChebT n)=Polynomial.Chebyshev.T ℚ (n:ℤ) :=
  (qChebT_pair_spec n).1
theorem qChebU_spec (n : ℕ) : qListPoly (qChebU n)=Polynomial.Chebyshev.U ℚ (n:ℤ) :=
  (qChebU_pair_spec n).1

def qListSum (ps : List (List ℚ)) : List ℚ := ps.foldl qListAdd []

theorem qListPoly_sum (ps : List (List ℚ)) : qListPoly (qListSum ps)=(ps.map qListPoly).sum := by
  have hh (ps : List (List ℚ)) (a : List ℚ) :
      qListPoly (ps.foldl qListAdd a)=qListPoly a+(ps.map qListPoly).sum := by
    induction ps generalizing a with
    | nil => simp
    | cons p ps ih => simp only [List.foldl_cons,ih,qListPoly_add,List.map_cons,List.sum_cons]; ring
  simpa only [qListSum,qListPoly,List.length_nil,Finset.range_zero,Finset.sum_empty,zero_add] using hh ps []

theorem qListPoly_sum_range (f : ℕ → List ℚ) (n : ℕ) :
    qListPoly (qListSum ((List.range n).map f))=∑ k ∈ Finset.range n,qListPoly (f k) := by
  rw [qListPoly_sum,List.map_map]
  simpa only [List.toFinset_range,Function.comp_def] using
    (List.sum_toFinset (fun k => qListPoly (f k)) (List.nodup_range (n:=n))).symm

def qDensityCoeffs (d : QSegment) : List ℚ :=
  qListSum ((List.range d.coeff.length).map (fun k : ℕ => qListScale (d.c k) (qChebT k)))
def qQuotDensityCoeffs (d : QSegment) : List ℚ :=
  qListSum ((List.range (d.coeff.length-1)).map (fun k : ℕ => qListScale (d.c (k+1)) (qChebU k)))
def qOwnCoeffs (d : QSegment) : List ℚ :=
  qListScale (-1) (qListSum ((List.range (d.coeff.length-1)).map (fun k : ℕ =>
    qListScale (d.c (k+1)/((k+1:ℕ):ℚ)) (qChebT (k+1)))))

theorem qDensityCoeffs_spec (d : QSegment) : qListPoly (qDensityCoeffs d)=d.density := by
  simp only [qDensityCoeffs,qListPoly_sum_range,qListPoly_scale,qChebT_spec,QSegment.density]

theorem qQuotDensityCoeffs_spec (d : QSegment) : qListPoly (qQuotDensityCoeffs d)=d.quotDensity := by
  simp only [qQuotDensityCoeffs,qListPoly_sum_range,qListPoly_scale,qChebU_spec,QSegment.quotDensity]

theorem qOwnCoeffs_spec (d : QSegment) : qListPoly (qOwnCoeffs d)=d.ownPolyQ := by
  simp only [qOwnCoeffs,qListPoly_scale,qListPoly_sum_range,qChebT_spec,QSegment.ownPolyQ]
  simp only [map_neg,map_one,neg_one_mul]

def qShiftList (p : List ℚ) (ζ γ : CQ) (j : ℕ) : CQ :=
  cqSum ((List.range p.length).map (fun k : ℕ =>
    if j ≤ k then cqScale (coeffQ p k*(CatalanCore.Uniform.Decay.Tools.chooseFast k j:ℚ))
      (cqMul (cqPow ζ (k-j)) (cqPow γ j)) else (0,0)))
noncomputable def qShiftCoeff (p : ℚ[X]) (ζ γ : CQ) (j : ℕ) : CQ :=
  cqSum ((List.range (p.natDegree+1)).map (fun k : ℕ =>
    if j ≤ k then cqScale (p.coeff k*(k.choose j:ℚ))
      (cqMul (cqPow ζ (k-j)) (cqPow γ j)) else (0,0)))

theorem cqSum_eq_sum (xs : List CQ) : cqSum xs=xs.sum := by
  change xs.foldl (fun a b : CQ => a+b) 0=xs.sum
  exact List.sum_eq_foldl.symm

theorem cqSum_range (f : ℕ → CQ) (n : ℕ) :
    cqSum ((List.range n).map f)=∑ k ∈ Finset.range n,f k := by
  rw [cqSum_eq_sum]
  simpa only [List.toFinset_range] using (List.sum_toFinset f (List.nodup_range (n:=n))).symm

theorem qListPoly_natDegree_lt (p : List ℚ) (hp : p ≠ []) : (qListPoly p).natDegree < p.length := by
  have hlen : 0 < p.length := by
    cases p with
    | nil => contradiction
    | cons a p => simp
  by_cases hz : qListPoly p=0
  · rw [hz,Polynomial.natDegree_zero]
    exact hlen
  · by_contra hh
    have hnz : (qListPoly p).coeff (qListPoly p).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hz
    have hzero := coeffQ_eq_zero_of_ge p (qListPoly p).natDegree (by omega)
    rw [← qListPoly_coeff] at hzero
    exact hnz hzero

theorem qShiftList_eq_spec (p : List ℚ) (ζ γ : CQ) (j : ℕ) :
    qShiftList p ζ γ j=qShiftCoeff (qListPoly p) ζ γ j := by
  by_cases hp : p=[]
  · subst p
    by_cases hj : j=0 <;> simp [qShiftList,qShiftCoeff,qListPoly,cqSum,cqScale,cqAdd,hj]
  · rw [qShiftList,qShiftCoeff,cqSum_range,cqSum_range]
    simp_rw [CatalanCore.Uniform.Decay.Tools.chooseFast_eq,qListPoly_coeff]
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_iff.mpr (qListPoly_natDegree_lt p hp)))
    intro k hk hnot
    have hdeg : (qListPoly p).natDegree < k := by
      have := Finset.mem_range.not.mp hnot
      omega
    have hz : coeffQ p k=0 := by
      rw [← qListPoly_coeff]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
    simp [hz,cqScale]

theorem qShiftList_density (d : QSegment) (ζ γ : CQ) (j : ℕ) :
    qShiftList (qDensityCoeffs d) ζ γ j=qShiftCoeff d.density ζ γ j := by
  rw [qShiftList_eq_spec,qDensityCoeffs_spec]
theorem qShiftList_quotDensity (d : QSegment) (ζ γ : CQ) (j : ℕ) :
    qShiftList (qQuotDensityCoeffs d) ζ γ j=qShiftCoeff d.quotDensity ζ γ j := by
  rw [qShiftList_eq_spec,qQuotDensityCoeffs_spec]
theorem qShiftList_own (d : QSegment) (ζ γ : CQ) (j : ℕ) :
    qShiftList (qOwnCoeffs d) ζ γ j=qShiftCoeff d.ownPolyQ ζ γ j := by
  rw [qShiftList_eq_spec,qOwnCoeffs_spec]

def qListDegree (p : List ℚ) : ℕ :=
  (0::((List.range p.length).filter (fun j : ℕ => decide (coeffQ p j ≠ 0)))).max (by simp)

theorem qListDegree_spec (p : List ℚ) : qListDegree p=(qListPoly p).natDegree := by
  apply le_antisymm
  · apply (List.max_le_iff (by simp)).mpr
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact Nat.zero_le _
    · simp only [List.mem_filter,List.mem_range,decide_eq_true_eq] at hj
      apply Polynomial.le_natDegree_of_ne_zero
      rw [qListPoly_coeff]
      exact hj.2
  · by_cases hz : qListPoly p=0
    · rw [hz,Polynomial.natDegree_zero]
      exact Nat.zero_le _
    · have hnz : (qListPoly p).coeff (qListPoly p).natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz
      have hc : coeffQ p (qListPoly p).natDegree ≠ 0 := by rwa [qListPoly_coeff] at hnz
      have hlen : (qListPoly p).natDegree < p.length := by
        by_contra hh
        exact hc (coeffQ_eq_zero_of_ge p _ (by omega))
      apply List.le_max_of_mem
      simp [List.mem_cons,List.mem_filter,List.mem_range,hlen,hc]

theorem qShiftCoeff_zero_of_degree_lt (p : ℚ[X]) (ζ γ : CQ) (j : ℕ) (hj : p.natDegree < j) :
    qShiftCoeff p ζ γ j=(0,0) := by
  rw [qShiftCoeff,cqSum_range]
  apply Finset.sum_eq_zero
  intro k hk
  have hkj : k < j := by have := Finset.mem_range.mp hk; omega
  simp only [show ¬j ≤ k by omega,ite_false]
  rfl

theorem qShiftList_zero_of_degree_lt (p : List ℚ) (ζ γ : CQ) (j : ℕ) (hj : qListDegree p < j) :
    qShiftList p ζ γ j=(0,0) := by
  rw [qListDegree_spec] at hj
  rw [qShiftList_eq_spec]
  exact qShiftCoeff_zero_of_degree_lt _ ζ γ j hj

#print axioms qShiftList_eq_spec
#print axioms qListDegree_spec
#print axioms qListDegree
end CatalanCore.Li2.DecayCert
