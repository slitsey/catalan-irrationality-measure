module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Lists
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open Polynomial Set
open scoped BigOperators
open CatalanCore.Uniform.Decay.Tools
namespace CatalanCore.Li2.DecayCert.LatticeGate

def qAffineList (p : List ℚ) (u v : ℚ) : List ℚ :=
  (List.range p.length).map (affK (coeffQ p) (p.length-1) u v)

theorem coeffQ_range_map (n i : ℕ) (f : ℕ→ℚ) :
    coeffQ ((List.range n).map f) i=if i<n then f i else 0 := by
  by_cases hi : i<n
  · simp [coeffQ,List.getElem?_range hi,hi]
  · have hh : ((List.range n).map f)[i]?=none := List.getElem?_eq_none (by simp;omega)
    simp [coeffQ,hh,hi]

private theorem qListPoly_eval_sum (p : List ℚ) (t : ℚ) :
    (qListPoly p).eval t=∑ j ∈ Finset.range p.length,coeffQ p j*t^j := by
  simp only [qListPoly,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]

theorem qAffineList_spec (p : List ℚ) (u v : ℚ) :
    qListPoly (qAffineList p u v)=(qListPoly p).comp (C u+C v*X) := by
  by_cases hp : p=[]
  · subst p
    simp [qAffineList,qListPoly]
  · have hn : p.length-1+1=p.length := by cases p <;>simp_all
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
    rw [qListPoly_eval_sum,qListPoly_eval_sum]
    have hl : (qAffineList p u v).length=p.length := by simp [qAffineList]
    rw [hl]
    calc
      _=∑ j ∈ Finset.range p.length,affK (coeffQ p) (p.length-1) u v j*t^j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [qAffineList,coeffQ_range_map,if_pos (Finset.mem_range.mp hj)]
      _=_ := by
        simpa only [peval,hn,affK_eq] using peval_affCoeffs (coeffQ p) (p.length-1) u v t

def linearPowerList (a b : ℚ) : ℕ→List ℚ
  | 0 => [1]
  | k+1 => qListAdd (qListScale a (linearPowerList a b k))
      (qListScale b (qListShift (linearPowerList a b k)))

theorem linearPowerList_spec (a b : ℚ) (k : ℕ) :
    qListPoly (linearPowerList a b k)=(C a+C b*X)^k := by
  induction k with
  | zero => simp [linearPowerList,qListPoly,coeffQ]
  | succ k ih =>
    rw [linearPowerList,qListPoly_add,qListPoly_scale,qListPoly_scale,qListPoly_shift,ih,pow_succ]
    ring

theorem coeff_contract_list (p : List ℚ) (f : ℕ→ℚ) :
    (∑ j ∈ Finset.range ((qListPoly p).natDegree+1),(qListPoly p).coeff j*f j)=
      ((List.range p.length).map (fun j=>coeffQ p j*f j)).sum := by
  by_cases hp : p=[]
  · subst p
    simp [qListPoly,coeffQ]
  · rw [list_sum_map_range]
    simp only [qListPoly_coeff]
    have hn : (qListPoly p).natDegree+1≤p.length := Nat.succ_le_iff.mpr (qListPoly_natDegree_lt p hp)
    apply Finset.sum_subset (Finset.range_mono hn)
    intro j hj hjout
    have hjn : (qListPoly p).natDegree<j := by
      simp only [Finset.mem_range] at hjout
      omega
    have hz : coeffQ p j=0 := by
      rw [← qListPoly_coeff]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hjn
    rw [hz,zero_mul]

theorem positiveArcMoment_fast (xi : ℚ) (k : ℕ) :
    arcList (linearPowerList xi (-1) k)=positiveArcMoment xi k := by
  rw [arcList_eq,linearPowerList_spec]
  unfold positiveArcMoment
  congr 1
  congr 1
  simp only [Polynomial.C_neg,Polynomial.C_1,neg_one_mul]
  ring

#print axioms qAffineList_spec
#print axioms coeff_contract_list
#print axioms positiveArcMoment_fast
def stieltjesFast (d : QSegment) (phi : ℚ) (k : ℕ) : ℚ :=
  let xi := (phi+phi⁻¹)/2
  let B := qAffineList (qDensityCoeffs d) (-xi) 1
  d.half.1^(-(k:ℤ))*((List.range B.length).map (fun i : ℕ=>coeffQ B i*
    (if i≤k then momentRec phi (k-i) else arcList (linearPowerList xi (-1) (i-k))))).sum

theorem stieltjesFast_eq (d : QSegment) (phi : ℚ) (k : ℕ) :
    stieltjesFast d phi k=stieltjesQ d phi k := by
  let xi := (phi+phi⁻¹)/2
  let B := qAffineList (qDensityCoeffs d) (-xi) 1
  have hB : qListPoly B=d.density.comp (X-C xi) := by
    dsimp only [B]
    rw [qAffineList_spec,qDensityCoeffs_spec]
    congr 1
    simp only [Polynomial.C_neg,Polynomial.C_1,one_mul]
    ring
  unfold stieltjesFast stieltjesQ
  change d.half.1^(-(k:ℤ))*((List.range B.length).map (fun i : ℕ=>coeffQ B i*
      (if i≤k then momentRec phi (k-i) else arcList (linearPowerList xi (-1) (i-k))))).sum=
    d.half.1^(-(k:ℤ))*(∑ i ∈ Finset.range ((d.density.comp (X-C xi)).natDegree+1),
      (d.density.comp (X-C xi)).coeff i*(if i≤k then momentRec phi (k-i) else positiveArcMoment xi (i-k)))
  rw [← hB,coeff_contract_list]
  simp only [positiveArcMoment_fast]

def stieltjesMomentFast (d : QSegment) (phi : ℚ) (K : ℕ) (sm : List ℚ) : Bool :=
  decide (1<phi ∧ 0<d.half.1 ∧ sm.length=K+1) &&
    (List.range (K+1)).all (fun k=>decide (coeffQ sm k=stieltjesFast d phi k))

theorem stieltjesMomentFast_eq (d : QSegment) (phi : ℚ) (K : ℕ) (sm : List ℚ) :
    stieltjesMomentFast d phi K sm=stieltjesMomentCheck d phi K sm := by
  simp only [stieltjesMomentFast,stieltjesMomentCheck,stieltjesFast_eq]

#print axioms stieltjesFast_eq
#print axioms stieltjesMomentFast_eq

end CatalanCore.Li2.DecayCert.LatticeGate
