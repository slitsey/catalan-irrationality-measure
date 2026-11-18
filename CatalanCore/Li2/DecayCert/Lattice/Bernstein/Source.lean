module
public import CatalanCore.Li2.DecayCert.Lattice.Bernstein.Basis
public import CatalanCore.Li2.DecayCert.Lattice.Bernstein.Engine
public import CatalanCore.Li2.DecayCert.Mass
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open Polynomial
open scoped BigOperators
open CatalanCore.Uniform.Decay.Tools
namespace CatalanCore.Li2.DecayCert.BernsteinGrid

def controlEval (bs : List ℚ) (t : ℚ) : ℚ :=
  ∑ k ∈ Finset.range bs.length,lget bs k*bw (bs.length-1) k t

theorem exactStep_length (S A B D c : ℤ) (ys : List ℚ) :
    (exactStep S A B D c ys).length=ys.length+1 := by
  cases ys <;> simp [exactStep]

theorem exactControls_length (S A B D : ℤ) (cs : List ℤ) :
    (exactControls S A B D cs).length=cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [exactControls,exactStep_length,ih]; rfl

theorem controlEval_nil (t : ℚ) : controlEval [] t=0 := by simp [controlEval]
theorem controlEval_singleton (c t : ℚ) : controlEval [c] t=c := by
  simp [controlEval,lget,bw]

theorem controlEval_exactStep (S A B D c : ℤ) (hD : D≠0) (ys : List ℚ) (t : ℚ) :
    controlEval (exactStep S A B D c ys) t=
      (c:ℚ)/(S:ℚ)+((A:ℚ)/(D:ℚ)*(1-t)+(B:ℚ)/(D:ℚ)*t)*controlEval ys t := by
  cases ys with
  | nil => simp [exactStep,controlEval_singleton,controlEval_nil]
  | cons y ys =>
    have hd : (D:ℚ)≠0 := by exact_mod_cast hD
    have hn : ((ys.length+1:ℕ):ℚ)≠0 := by positivity
    unfold controlEval
    rw [exactStep_length]
    dsimp only [exactStep]
    simp only [List.length_cons,Nat.add_sub_cancel,Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
    have he (k : ℕ) (hk : k<ys.length+2) :
        lget ((List.range ((y::ys).length+1)).map (fun k : ℕ =>
          (c:ℚ)/(S:ℚ)+((( (y::ys).length-k:ℕ):ℚ)*(A:ℚ)*lget (y::ys) k+
          (k:ℚ)*(B:ℚ)*(if k=0 then 0 else lget (y::ys) (k-1)))/
          (((y::ys).length:ℚ)*(D:ℚ)))) k=
        blendCoeff ys.length k ((c:ℚ)/(S:ℚ)) ((A:ℚ)/(D:ℚ)) ((B:ℚ)/(D:ℚ)) (lget (y::ys)) := by
      rw [lget_map_range,if_pos (by simp only [List.length_cons]; omega)]
      unfold blendCoeff
      simp only [List.length_cons]
      field_simp
      <;> ring
    calc
      _=∑ k ∈ Finset.range (ys.length+2),
          blendCoeff ys.length k ((c:ℚ)/(S:ℚ)) ((A:ℚ)/(D:ℚ)) ((B:ℚ)/(D:ℚ)) (lget (y::ys))*bw (ys.length+1) k t := by
        apply Finset.sum_congr rfl
        intro k hk
        exact congrArg (fun z : ℚ => z*bw (ys.length+1) k t) (he k (by have := Finset.mem_range.mp hk; omega))
      _=_ := bezier_blend _ _ _ _ _ _

theorem controlEval_exactControls (S A B D : ℤ) (hD : D≠0) (cs : List ℤ) (t : ℚ) :
    controlEval (exactControls S A B D cs) t=
      qEval (cs.map (fun c : ℤ => (c:ℚ)/(S:ℚ)))
        ((A:ℚ)/(D:ℚ)*(1-t)+(B:ℚ)/(D:ℚ)*t) := by
  induction cs with
  | nil => simp [exactControls,controlEval_nil,qEval]
  | cons c cs ih =>
    rw [exactControls,controlEval_exactStep _ _ _ _ _ hD,ih]
    rfl

#print axioms controlEval_exactStep
#print axioms controlEval_exactControls
theorem bernCoeff_eval (p : ℚ[X]) (a b : ℚ) (n : ℕ) (hn : p.natDegree≤n) (t : ℚ) :
    (∑ k ∈ Finset.range (n+1),bernCoeff p a b n k*bw n k t)=p.eval (a+(b-a)*t) := by
  simp only [bernCoeff,bernK_eq,affK_eq]
  rw [← peval_eq_bern_sum,peval_affCoeffs]
  exact (Polynomial.eval_eq_sum_range' (by omega : p.natDegree<n+1) _).symm

theorem controlEval_unique (xs ys : List ℚ) (hl : xs.length=ys.length)
    (he : ∀ t : ℚ,controlEval xs t=controlEval ys t) : xs=ys := by
  cases xs with
  | nil => exact (List.eq_nil_of_length_eq_zero hl.symm).symm
  | cons x xs =>
    have hp : bernPoly xs.length (fun i => lget (x::xs) i)=
        bernPoly xs.length (fun i => lget ys i) := by
      apply Polynomial.funext
      intro t
      rw [bernPoly_eval,bernPoly_eval]
      have hh := he t
      unfold controlEval at hh
      rw [← hl] at hh
      simp only [List.length_cons,Nat.add_sub_cancel] at hh
      rw [← Fin.sum_univ_eq_sum_range,← Fin.sum_univ_eq_sum_range] at hh
      exact hh
    have hc := bernPoly_injective xs.length hp
    apply List.ext_getElem?
    intro i
    by_cases hi : i<(x::xs).length
    · have hj : i<ys.length := by omega
      have hh := congrFun hc ⟨i,by simpa using hi⟩
      simpa only [lget,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some]
        using congrArg some hh
    · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

theorem exactControls_bernCoeff (S A B D : ℤ) (hD : D≠0) (cs : List ℤ) (hne : cs≠[]) :
    exactControls S A B D cs=(List.range cs.length).map
      (bernCoeff (qListPoly (cs.map (fun c : ℤ => (c:ℚ)/(S:ℚ))))
        ((A:ℚ)/(D:ℚ)) ((B:ℚ)/(D:ℚ)) (cs.length-1)) := by
  apply controlEval_unique
  · simp [exactControls_length]
  · intro t
    rw [controlEval_exactControls _ _ _ _ hD,qEval_correct]
    have hn : 0<cs.length := by cases cs <;> simp_all
    have hp := qListPoly_natDegree_lt (cs.map (fun c : ℤ => (c:ℚ)/(S:ℚ))) (by simpa using hne)
    unfold controlEval
    simp only [List.length_map,List.length_range]
    have hs : cs.length=cs.length-1+1 := by omega
    calc
      _=(qListPoly (cs.map (fun c : ℤ => (c:ℚ)/(S:ℚ)))).eval
          ((A:ℚ)/(D:ℚ)+((B:ℚ)/(D:ℚ)-(A:ℚ)/(D:ℚ))*t) := by congr 1 <;> ring
      _=∑ k ∈ Finset.range cs.length,bernCoeff (qListPoly (cs.map (fun c : ℤ => (c:ℚ)/(S:ℚ))))
            ((A:ℚ)/(D:ℚ)) ((B:ℚ)/(D:ℚ)) (cs.length-1) k*bw (cs.length-1) k t := by
        simpa only [← hs] using (bernCoeff_eval _ _ _ (cs.length-1) (by simp only [List.length_map] at hp;omega) t).symm
      _=_ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [lget_map_range,if_pos (Finset.mem_range.mp hk)]

#print axioms exactControls_bernCoeff

def decodedBoxes (S : ℤ) (xs : List (ℤ×ℤ)) : List (ℚ×ℚ) :=
  xs.map (fun b=>((b.1:ℚ)/(S:ℚ),(b.2:ℚ)/(S:ℚ)))

theorem lget_decodedBoxes (S : ℤ) (xs : List (ℤ×ℤ)) (i : ℕ) :
    lget (decodedBoxes S xs) i=((lget xs i).1/(S:ℚ),(lget xs i).2/(S:ℚ)) := by
  cases hh : xs[i]? <;> simp [decodedBoxes,lget,hh] <;> rfl

theorem bernInts_coefficient (S A B D : ℤ) (hS : 0<S) (hD : 0<D)
    (cs : List ℤ) (k : ℕ) (hk : k<cs.length) :
    Encloses S (lget (bernInts A B D cs) k)
      (bernCoeff (qListPoly (cs.map (fun c : ℤ => (c:ℚ)/(S:ℚ))))
        ((A:ℚ)/(D:ℚ)) ((B:ℚ)/(D:ℚ)) (cs.length-1) k) := by
  have h := bernInts_sound S A B D hS hD cs
  rw [exactControls_bernCoeff S A B D hD.ne' cs (by intro hh;subst cs;simp at hk)] at h
  simpa only [lget_map_range,hk,ite_true] using h.2 k

theorem bernInts_BoxRep (S : ℤ) (hS : 0<S) (cs : List ℤ) :
    BoxRep (cs.map (fun c : ℤ => (c:ℚ)/(S:ℚ)))
      (decodedBoxes S (bernInts (-1) 1 1 cs)) := by
  have hs : (0:ℚ)<(S:ℚ) := by exact_mod_cast hS
  refine ⟨by simp [decodedBoxes,bernInts_length],?_⟩
  intro k hk
  simp only [List.length_map] at hk
  have h := bernInts_coefficient S (-1) 1 1 hS (by decide) cs k hk
  simp only [Int.cast_neg,Int.cast_one,div_one] at h
  change (lget (decodedBoxes S (bernInts (-1) 1 1 cs)) k).1≤_ ∧
    _≤(lget (decodedBoxes S (bernInts (-1) 1 1 cs)) k).2
  rw [lget_decodedBoxes]
  simp only [List.length_map]
  exact ⟨(div_le_iff₀ hs).2 (by simpa only [mul_comm] using h.1),
    (le_div_iff₀ hs).2 (by simpa only [mul_comm] using h.2)⟩

#print axioms bernInts_BoxRep

end CatalanCore.Li2.DecayCert.BernsteinGrid
