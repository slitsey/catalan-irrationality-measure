module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Moments
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open Polynomial Set
open scoped BigOperators
open CatalanCore.Uniform.Decay.Tools
namespace CatalanCore.Li2.DecayCert.LatticeGate

def bernCoeffFast (p : List ℚ) (a b : ℚ) (N k : ℕ) : ℚ :=
  bernK (affK (coeffQ p) N a (b-a)) N k

theorem bernCoeffFast_eq (p : List ℚ) (a b : ℚ) (N k : ℕ) :
    bernCoeffFast p a b N k=bernCoeff (qListPoly p) a b N k := by
  unfold bernCoeffFast bernCoeff
  rw [show (qListPoly p).coeff=coeffQ p from funext (qListPoly_coeff p)]

def bernListCheck (p : List ℚ) : ℚ→ℚ→BernsteinTree→Bool
  | a,b,.leaf N cs => decide (a≤b ∧ qListDegree p≤N ∧ cs.length=N+1 ∧
      cs=(List.range (N+1)).map (bernCoeffFast p a b N) ∧ ∀ c∈cs,0≤c)
  | a,b,.split mid L R => decide (a<mid ∧ mid<b) && bernListCheck p a mid L && bernListCheck p mid b R

theorem bernListCheck_eq (p : List ℚ) (a b : ℚ) (t : BernsteinTree) :
    bernListCheck p a b t=bernCheck (qListPoly p) a b t := by
  induction t generalizing a b with
  | leaf N cs =>
    simp only [bernListCheck,bernCheck,qListDegree_spec]
    rw [show bernCoeffFast p a b N=bernCoeff (qListPoly p) a b N from funext (bernCoeffFast_eq p a b N)]
  | split mid L R ihL ihR => simp only [bernListCheck,bernCheck,ihL,ihR]

def arcList (p : List ℚ) : ℚ :=
  ((List.range p.length).map (fun j : ℕ=>if Even j then
    coeffQ p j*((chooseFast j (j/2):ℚ)/4^(j/2)) else 0)).sum

theorem arcList_eq (p : List ℚ) : arcList p=arcPolyMoment (qListPoly p) := by
  by_cases hp : p=[]
  · subst p
    simp [arcList,arcPolyMoment,qListPoly]
  · have hn : (qListPoly p).natDegree+1≤p.length := Nat.succ_le_iff.mpr (qListPoly_natDegree_lt p hp)
    rw [arcList,list_sum_map_range]
    simp only [chooseFast_eq,arcPolyMoment,qListPoly_coeff]
    symm
    apply Finset.sum_subset (Finset.range_mono hn)
    intro j hj hjout
    have hjn : (qListPoly p).natDegree<j := by
      simp only [Finset.mem_range] at hjout
      omega
    have hz : coeffQ p j=0 := by
      rw [← qListPoly_coeff]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hjn
    simp [hz]

def realMomentList (d : QSegment) (y0 : ℚ) : ℕ→List ℚ
  | 0 => qDensityCoeffs d
  | k+1 => qListAdd (qListScale (d.mid.1-y0) (realMomentList d y0 k))
      (qListScale d.half.1 (qListShift (realMomentList d y0 k)))

theorem realMomentList_spec (d : QSegment) (y0 : ℚ) (k : ℕ) :
    qListPoly (realMomentList d y0 k)=d.density*(C (d.mid.1-y0)+C d.half.1*X)^k := by
  induction k with
  | zero => simp only [realMomentList,qDensityCoeffs_spec,pow_zero,mul_one]
  | succ k ih =>
    rw [realMomentList,qListPoly_add,qListPoly_scale,qListPoly_scale,qListPoly_shift,ih,pow_succ]
    ring

def ordinaryMomentFast (d : QSegment) (y0 : ℚ) (K : ℕ) (mu : List ℚ) : Bool :=
  decide (0<d.coeff.length ∧ d.mid.2=0 ∧ d.half.2=0 ∧ mu.length=K+1) &&
    (List.range (K+1)).all (fun k=>decide (coeffQ mu k=arcList (realMomentList d y0 k)))

theorem ordinaryMomentFast_eq (d : QSegment) (y0 : ℚ) (K : ℕ) (mu : List ℚ) :
    ordinaryMomentFast d y0 K mu=ordinaryMomentCheck d y0 K mu := by
  simp only [ordinaryMomentFast,ordinaryMomentCheck,arcList_eq,realMomentList_spec]

#print axioms bernListCheck_eq
#print axioms arcList_eq
#print axioms realMomentList_spec
#print axioms ordinaryMomentFast_eq
end CatalanCore.Li2.DecayCert.LatticeGate
