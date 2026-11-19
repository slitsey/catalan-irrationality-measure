module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Numeric
public import CatalanArchive.Li2.DecayCert.Lattice.Gates.Penalty.Analytic
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open Polynomial Set MeasureTheory
open scoped BigOperators
open CatalanCore.Li2.Decay
namespace CatalanCore.Li2.DecayCert.LatticeGate
open BernsteinGrid

def penaltyBoxQ (S err lo hi : ℤ) (a b : ℚ) (boxes : List (ℤ×ℤ)) : ℚ :=
  if hi≤0 then 0 else if 0≤lo then
    max ((b-a)*(upperMeanQ (decodedBoxes S boxes)+(err:ℚ)/(S:ℚ))) 0
  else (b-a)*max ((hi:ℚ)/(S:ℚ)) 0

def bernPenaltyCheck (S err lo hi : ℤ) (a b E : ℚ) (boxes : List (ℤ×ℤ)) : Bool :=
  decide (-1≤a ∧ a≤b ∧ b≤1) && bernLeafCheck S err lo hi E boxes

theorem bernPenaltyCheck_sound (S err lo hi : ℤ) (a b E : ℚ) (boxes : List (ℤ×ℤ))
    (f : ℝ→ℝ) (co : List ℚ) (hne : co≠[])
    (hf : ContinuousOn f (Icc (a:ℝ) (b:ℝ)))
    (hm : ModelsOn f (co.map (fun q : ℚ => (q:ℝ))) (-1) 1 E)
    (ht : TableEncloses S boxes (canonicalControls (qListPoly co) a b (co.length-1)))
    (hc : bernPenaltyCheck S err lo hi a b E boxes=true) :
    (∫x in (a:ℝ)..(b:ℝ),pos (f x))≤(penaltyBoxQ S err lo hi a b boxes:ℝ) := by
  have hh : (-1≤a ∧ a≤b ∧ b≤1) ∧ bernLeafCheck S err lo hi E boxes=true := by
    simpa only [bernPenaltyCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
  rcases hh with ⟨⟨ha,hab,hb⟩,hleaf⟩
  have hgeom : 0<S ∧ E≤(err:ℚ)/(S:ℚ) := by
    have hh := hleaf
    simp only [bernLeafCheck,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.1
  have hpoint := bernLeafCheck_sound S err lo hi E boxes f co hne a b hab ha hb hm ht hleaf
  simp only [← Rat.cast_div] at hpoint
  have hs : (0:ℚ)<(S:ℚ) := by exact_mod_cast hgeom.1
  have habR : (a:ℝ)≤(b:ℝ) := by exact_mod_cast hab
  by_cases hhi : hi≤0
  · have hupper : (((hi:ℚ)/(S:ℚ):ℚ):ℝ)≤0 := by
      exact_mod_cast (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hhi : (hi:ℚ)≤0) hs.le)
    have hp := pos_integral_zero f (a:ℝ) (b:ℝ) habR (fun x hx=>(hpoint x hx).2.trans hupper)
    simpa only [penaltyBoxQ,hhi,ite_true,Rat.cast_zero] using hp.le
  · by_cases hlo : 0≤lo
    · have hlower : (0:ℝ)≤(((lo:ℚ)/(S:ℚ):ℚ):ℝ) := by
        exact_mod_cast (div_nonneg (by exact_mod_cast hlo : (0:ℚ)≤lo) hs.le)
      have hfloor : ∀x∈Icc (a:ℝ) (b:ℝ),0≤f x := fun x hx=>hlower.trans (hpoint x hx).1
      have hbox := tableEncloses_CellBoxRep S hgeom.1 boxes _ a b _ ht
      have hp := positive_model_integral f co hne a b E hab ha hb hf hm
        (decodedBoxes S boxes) hbox hfloor
      simp only [penaltyBoxQ,hhi,hlo,ite_false,ite_true,Rat.cast_max,Rat.cast_zero]
      apply le_trans ?_ (le_max_left _ 0)
      have herr : (E:ℝ)≤(((err:ℚ)/(S:ℚ):ℚ):ℝ) := by exact_mod_cast hgeom.2
      push_cast at herr ⊢
      apply hp.trans
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr habR)
      linarith
    · have hp := pos_integral_constant f (a:ℝ) (b:ℝ) (((hi:ℚ)/(S:ℚ):ℚ):ℝ) habR hf
        (fun x hx=>(hpoint x hx).2)
      simpa only [penaltyBoxQ,hhi,hlo,ite_false,Rat.cast_mul,Rat.cast_sub,Rat.cast_max,Rat.cast_zero] using hp

def bernPenaltyBoundCheck (S err lo hi : ℤ) (a b E cap : ℚ)
    (boxes : List (ℤ×ℤ)) : Bool :=
  bernPenaltyCheck S err lo hi a b E boxes && decide (penaltyBoxQ S err lo hi a b boxes≤cap)

theorem bernPenaltyBoundCheck_sound (S err lo hi : ℤ) (a b E cap : ℚ) (boxes : List (ℤ×ℤ))
    (f : ℝ→ℝ) (co : List ℚ) (hne : co≠[])
    (hf : ContinuousOn f (Icc (a:ℝ) (b:ℝ)))
    (hm : ModelsOn f (co.map (fun q : ℚ => (q:ℝ))) (-1) 1 E)
    (ht : TableEncloses S boxes (canonicalControls (qListPoly co) a b (co.length-1)))
    (hc : bernPenaltyBoundCheck S err lo hi a b E cap boxes=true) :
    (∫x in (a:ℝ)..(b:ℝ),pos (f x))≤(cap:ℝ) := by
  have hh : bernPenaltyCheck S err lo hi a b E boxes=true ∧ penaltyBoxQ S err lo hi a b boxes≤cap := by
    simpa only [bernPenaltyBoundCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
  exact (bernPenaltyCheck_sound S err lo hi a b E boxes f co hne hf hm ht hh.1).trans (by exact_mod_cast hh.2)

#print axioms bernPenaltyCheck_sound
#print axioms bernPenaltyBoundCheck_sound
end CatalanCore.Li2.DecayCert.LatticeGate
