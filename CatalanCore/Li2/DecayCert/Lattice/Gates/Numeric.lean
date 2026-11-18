module
public import CatalanCore.Li2.DecayCert.Lattice.Bernstein
public import CatalanCore.Li2.DecayCert.Compile
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open Polynomial Set
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeGate
open BernsteinGrid

def bernParentCheck (S : ℤ) (m : CompiledModel) (w : CellWitness)
    (boxes : List (ℤ×ℤ)) : Bool :=
  decide (0<S ∧ w.coeff≠[]) && coefficientCheck S m w && remainderCheck S 1 m w &&
    decide (bernInts (-1) 1 1 w.coeff=boxes)

theorem bernParentCheck_parts (S : ℤ) (m : CompiledModel) (w : CellWitness)
    (boxes : List (ℤ×ℤ)) (hc : bernParentCheck S m w boxes=true) :
    (0<S ∧ w.coeff≠[]) ∧ coefficientCheck S m w=true ∧ remainderCheck S 1 m w=true ∧
      bernInts (-1) 1 1 w.coeff=boxes := by
  simpa only [bernParentCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc

theorem bernParentCheck_sound (S : ℤ) (m : CompiledModel) (w : CellWitness)
    (boxes : List (ℤ×ℤ)) (f : ℝ→ℝ)
    (hm : ModelsOn f (m.coeff.map ScalarExpr.value) (-1) 1 m.error.value)
    (hc : bernParentCheck S m w boxes=true) :
    ModelsOn f ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) (-1) 1 w.remainder ∧
      BoxRep (gridCoeffs S w) (decodedBoxes S boxes) := by
  rcases bernParentCheck_parts S m w boxes hc with ⟨⟨hS,hne⟩,hco,hr,hbox⟩
  constructor
  · have hm' : ModelsOn f (m.coeff.map ScalarExpr.value) ((-1:ℚ):ℝ) ((1:ℚ):ℝ) m.error.value := by
      simpa only [Rat.cast_neg,Rat.cast_one] using hm
    have hr' : remainderCheck S (max |(-1:ℚ)| |1|) m w=true := by
      simpa only [abs_neg,abs_one,max_self] using hr
    simpa only [Rat.cast_neg,Rat.cast_one] using roundModel_sound S (-1) 1 m w f hm' hco hr' 
  · rw [← hbox]
    exact bernInts_BoxRep S hS w.coeff

theorem bernParentCheck_table (S : ℤ) (m : CompiledModel) (w : CellWitness)
    (boxes : List (ℤ×ℤ)) (hc : bernParentCheck S m w boxes=true) :
    TableEncloses S boxes (canonicalControls (qListPoly (gridCoeffs S w)) (-1) 1 (w.coeff.length-1)) := by
  rcases bernParentCheck_parts S m w boxes hc with ⟨⟨hS,hne⟩,hco,hr,hbox⟩
  have h := bernInts_sound S (-1) 1 1 hS (by decide) w.coeff
  rw [exactControls_bernCoeff S (-1) 1 1 (by decide) w.coeff hne] at h
  rw [hbox] at h
  have hl : w.coeff.length=w.coeff.length-1+1 := by cases hh : w.coeff <;> simp_all
  simpa only [canonicalControls,gridCoeffs,← hl,Int.cast_neg,Int.cast_one,div_one] using h

def bernSplitCheck (parent left right : List (ℤ×ℤ)) : Bool :=
  decide (splitInts parent=(left,right))

theorem bernSplitCheck_sound (S : ℤ) (hS : 0<S)
    (p : ℚ[X]) (a b : ℚ) (n : ℕ) (hn : p.natDegree≤n)
    (parent left right : List (ℤ×ℤ))
    (hp : TableEncloses S parent (canonicalControls p a b n))
    (hc : bernSplitCheck parent left right=true) :
    TableEncloses S left (canonicalControls p a ((a+b)/2) n) ∧
      TableEncloses S right (canonicalControls p ((a+b)/2) b n) := by
  have hh : splitInts parent=(left,right) := of_decide_eq_true hc
  have h := splitInts_canonical S hS parent p a b n hn hp
  simpa only [hh] using h

/-- Cheap leaf check. All bounds and controls are Int grid numerators. -/
def bernLeafCheck (S err lo hi : ℤ) (E : ℚ) (boxes : List (ℤ×ℤ)) : Bool :=
  decide (0<S ∧ E≤(err:ℚ)/(S:ℚ)) &&
    boxes.all (fun b=>decide (lo+err≤b.1 ∧ b.2+err≤hi))

theorem bernLeafCheck_sound (S err lo hi : ℤ) (E : ℚ) (boxes : List (ℤ×ℤ))
    (f : ℝ→ℝ) (co : List ℚ) (hne : co≠[]) (a b : ℚ)
    (hab : a≤b) (ha : -1≤a) (hb : b≤1)
    (hm : ModelsOn f (co.map (fun q : ℚ => (q:ℝ))) (-1) 1 E)
    (ht : TableEncloses S boxes (canonicalControls (qListPoly co) a b (co.length-1)))
    (hc : bernLeafCheck S err lo hi E boxes=true) :
    ∀ x∈Icc (a:ℝ) (b:ℝ), ((lo:ℚ)/(S:ℚ):ℝ)≤f x ∧ f x≤((hi:ℚ)/(S:ℚ):ℝ) := by
  have hh : (0<S ∧ E≤(err:ℚ)/(S:ℚ)) ∧
      ∀ c∈boxes,lo+err≤c.1 ∧ c.2+err≤hi := by
    simpa only [bernLeafCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] using hc
  have hs : (0:ℚ)<(S:ℚ) := by exact_mod_cast hh.1.1
  have hbox := tableEncloses_CellBoxRep S hh.1.1 boxes _ a b _ ht
  have hl : ∀ c∈decodedBoxes S boxes,((lo+err:ℤ):ℚ)/(S:ℚ)≤c.1 := by
    intro c hc
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hc
    apply (div_le_div_iff_of_pos_right hs).2
    exact_mod_cast (hh.2 z hz).1
  have hu : ∀ c∈decodedBoxes S boxes,c.2≤((hi-err:ℤ):ℚ)/(S:ℚ) := by
    intro c hc
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hc
    apply (div_le_div_iff_of_pos_right hs).2
    exact_mod_cast (by linarith [(hh.2 z hz).2] : z.2≤hi-err)
  have hp := normalized_child_model_bounds f co a b E
    (((lo+err:ℤ):ℚ)/(S:ℚ)) (((hi-err:ℤ):ℚ)/(S:ℚ))
    (decodedBoxes S boxes) hne hab ha hb hm hbox hl hu
  intro x hx
  have h := hp x hx
  have herr : (E:ℝ)≤((err:ℚ)/(S:ℚ):ℝ) := by exact_mod_cast hh.1.2
  push_cast at h herr ⊢
  rw [add_div,sub_div] at h
  constructor <;> linarith

#print axioms bernParentCheck_sound
#print axioms bernParentCheck_table
#print axioms bernSplitCheck_sound
#print axioms bernLeafCheck_sound
end CatalanCore.Li2.DecayCert.LatticeGate
