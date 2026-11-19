module
public import CatalanArchive.Li2.DecayCert.Lattice.Gates.Parents
public import CatalanArchive.Li2.DecayCert.Lattice.Gates.Penalty
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
open Polynomial Set
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeGate
open BernsteinGrid CatalanCore.Li2.Decay

def childInterval : List Bool → ℚ → ℚ → ℚ×ℚ
  | [],a,b => (a,b)
  | left::path,a,b => if left then childInterval path a ((a+b)/2)
      else childInterval path ((a+b)/2) b

def childBoxes : List Bool → List (ℤ×ℤ) → List (ℤ×ℤ)
  | [],boxes => boxes
  | left::path,boxes => childBoxes path (if left then (splitInts boxes).1 else (splitInts boxes).2)

theorem childInterval_bounds (path : List Bool) (a b : ℚ)
    (hab : a≤b) (ha : -1≤a) (hb : b≤1) :
    -1≤(childInterval path a b).1 ∧ (childInterval path a b).1≤(childInterval path a b).2 ∧
      (childInterval path a b).2≤1 := by
  induction path generalizing a b with
  | nil => exact ⟨ha,hab,hb⟩
  | cons left path ih =>
    cases left
    · simpa only [childInterval,Bool.false_eq_true,ite_false] using
        ih ((a+b)/2) b (by linarith) (by linarith) hb
    · simpa only [childInterval,ite_true] using
        ih a ((a+b)/2) (by linarith) ha (by linarith)

theorem childBoxes_canonical (S : ℤ) (hS : 0<S) (p : ℚ[X]) (n : ℕ)
    (hn : p.natDegree≤n) (path : List Bool) (a b : ℚ) (boxes : List (ℤ×ℤ))
    (ht : TableEncloses S boxes (canonicalControls p a b n)) :
    TableEncloses S (childBoxes path boxes)
      (canonicalControls p (childInterval path a b).1 (childInterval path a b).2 n) := by
  induction path generalizing a b boxes with
  | nil => exact ht
  | cons left path ih =>
    have hs := splitInts_canonical S hS boxes p a b n hn ht
    cases left
    · simpa only [childBoxes,childInterval,Bool.false_eq_true,ite_false] using
        ih ((a+b)/2) b (splitInts boxes).2 hs.2
    · simpa only [childBoxes,childInterval,ite_true] using
        ih a ((a+b)/2) (splitInts boxes).1 hs.1

def macroLeafCheck (S : ℤ) (w : CellWitness) (root : List (ℤ×ℤ))
    (path : List Bool) (err lo hi : ℤ) (boxes : List (ℤ×ℤ)) : Bool :=
  decide (0<S ∧ w.coeff≠[]) && decide (childBoxes path root=boxes) &&
    bernLeafCheck S err lo hi w.remainder boxes

theorem macroLeafCheck_table (S : ℤ) (w : CellWitness) (root : List (ℤ×ℤ))
    (path : List Bool) (err lo hi : ℤ) (boxes : List (ℤ×ℤ))
    (ht : TableEncloses S root (canonicalControls (qListPoly (gridCoeffs S w)) (-1) 1 (w.coeff.length-1)))
    (hc : macroLeafCheck S w root path err lo hi boxes=true) :
    TableEncloses S boxes (canonicalControls (qListPoly (gridCoeffs S w))
      (childInterval path (-1) 1).1 (childInterval path (-1) 1).2 (w.coeff.length-1)) := by
  have hh : (0<S ∧ w.coeff≠[]) ∧ childBoxes path root=boxes ∧
      bernLeafCheck S err lo hi w.remainder boxes=true := by
    simpa only [macroLeafCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc
  have hne : gridCoeffs S w≠[] := by
    intro hz
    have hl := congrArg List.length hz
    simp only [gridCoeffs,List.length_map,List.length_nil] at hl
    exact hh.1.2 (List.eq_nil_of_length_eq_zero hl)
  have hn := qListPoly_natDegree_lt (gridCoeffs S w) hne
  have ht' := childBoxes_canonical S hh.1.1 _ (w.coeff.length-1)
    (by
      have hl : (gridCoeffs S w).length=w.coeff.length := by simp [gridCoeffs]
      rw [hl] at hn
      omega) path (-1) 1 root ht
  simpa only [hh.2.1] using ht'

theorem macroLeafCheck_sound (S : ℤ) (w : CellWitness) (root : List (ℤ×ℤ))
    (path : List Bool) (err lo hi : ℤ) (boxes : List (ℤ×ℤ)) (f : ℝ→ℝ)
    (hm : ModelsOn f ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) (-1) 1 w.remainder)
    (ht : TableEncloses S root (canonicalControls (qListPoly (gridCoeffs S w)) (-1) 1 (w.coeff.length-1)))
    (hc : macroLeafCheck S w root path err lo hi boxes=true) :
    ∀x∈Icc (((childInterval path (-1) 1).1:ℚ):ℝ) (((childInterval path (-1) 1).2:ℚ):ℝ),
      ((lo:ℚ)/(S:ℚ):ℝ)≤f x ∧ f x≤((hi:ℚ)/(S:ℚ):ℝ) := by
  have hh : (0<S ∧ w.coeff≠[]) ∧ childBoxes path root=boxes ∧
      bernLeafCheck S err lo hi w.remainder boxes=true := by
    simpa only [macroLeafCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc
  have hd := childInterval_bounds path (-1) 1 (by norm_num) le_rfl le_rfl
  have hne : gridCoeffs S w≠[] := by
    intro hz
    have hl := congrArg List.length hz
    simp only [gridCoeffs,List.length_map,List.length_nil] at hl
    exact hh.1.2 (List.eq_nil_of_length_eq_zero hl)
  have ht' := macroLeafCheck_table S w root path err lo hi boxes ht hc
  have hl : (gridCoeffs S w).length=w.coeff.length := by simp [gridCoeffs]
  rw [← hl] at ht'
  exact bernLeafCheck_sound S err lo hi w.remainder boxes f (gridCoeffs S w) hne _ _
    hd.2.1 hd.1 hd.2.2 hm ht' hh.2.2

theorem WMacroLeafCheck_sound (terms : ℕ) (z : ℚ) (hz : z≠0) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (p r y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (root : List (ℤ×ℤ))
    (hp : WMacroParentCheck terms z d p r y0 L Y H mu K J base S w root=true)
    (path : List Bool) (err lo hi : ℤ) (boxes : List (ℤ×ℤ))
    (hc : macroLeafCheck S w root path err lo hi boxes=true) :
    ∀t∈Icc (((childInterval path (-1) 1).1:ℚ):ℝ) (((childInterval path (-1) 1).2:ℚ):ℝ),
      ((lo:ℚ)/(S:ℚ):ℝ)≤W (z:ℝ) d.data.dual.σ (((p:ℝ)+(r:ℝ)*t:ℝ):ℂ) ∧
      W (z:ℝ) d.data.dual.σ (((p:ℝ)+(r:ℝ)*t:ℝ):ℂ)≤((hi:ℚ)/(S:ℚ):ℝ) := by
  have hs := WMacroParentCheck_sound terms z hz d dw hd p r y0 L Y H mu K J base S w root hp
  exact macroLeafCheck_sound S w root path err lo hi boxes _ hs.1 hs.2 hc

theorem atomMacroLeafCheck_sound (terms : ℕ) (z : ℚ) (hz : z≠0) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (p r phi Y R : ℚ) (sm : List ℚ) (K : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (root : List (ℤ×ℤ))
    (hp : atomMacroParentCheck terms z d p r phi Y R sm K base S w root=true)
    (path : List Bool) (err lo hi : ℤ) (boxes : List (ℤ×ℤ))
    (hc : macroLeafCheck S w root path err lo hi boxes=true) :
    ∀t∈Icc (((childInterval path (-1) 1).1:ℚ):ℝ) (((childInterval path (-1) 1).2:ℚ):ℝ),
      ((lo:ℚ)/(S:ℚ):ℝ)≤omega (z:ℝ) ((p:ℝ)+(r:ℝ)*t)-
        2*U d.data.dual.σ (-(((p:ℝ)+(r:ℝ)*t:ℝ):ℂ)) ∧
      omega (z:ℝ) ((p:ℝ)+(r:ℝ)*t)-2*U d.data.dual.σ (-(((p:ℝ)+(r:ℝ)*t:ℝ):ℂ))≤
        ((hi:ℚ)/(S:ℚ):ℝ) := by
  have hs := atomMacroParentCheck_sound terms z hz d dw hd p r phi Y R sm K base S w root hp
  exact macroLeafCheck_sound S w root path err lo hi boxes _ hs.1 hs.2 hc
#print axioms childBoxes_canonical
#print axioms macroLeafCheck_sound
#print axioms WMacroLeafCheck_sound
#print axioms atomMacroLeafCheck_sound
end CatalanCore.Li2.DecayCert.LatticeGate
