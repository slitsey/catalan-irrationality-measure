module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Numeric
public import CatalanCore.Li2.DecayCert.SourceBridge
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open Polynomial Set
open scoped BigOperators
open CatalanCore.Li2.Decay
namespace CatalanCore.Li2.DecayCert.LatticeGate
open BernsteinGrid

noncomputable def compiledBernParentCheck (S : ℤ) (e : CellExpr) (w : CellWitness)
    (boxes : List (ℤ×ℤ)) : Bool :=
  match compileModel (-1) 1 e w.model with
  | none => false
  | some m => bernParentCheck S m w boxes

theorem compiledBernParentCheck_sound (S : ℤ) (e : CellExpr) (w : CellWitness)
    (boxes : List (ℤ×ℤ)) (hp : PositiveSources e)
    (hc : compiledBernParentCheck S e w boxes=true) :
    ModelsOn e.value ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) (-1) 1 w.remainder ∧
      BoxRep (gridCoeffs S w) (decodedBoxes S boxes) := by
  unfold compiledBernParentCheck at hc
  cases hh : compileModel (-1) 1 e w.model with
  | none => simp only [hh,Bool.false_eq_true] at hc
  | some m =>
    rw [hh] at hc
    have hm := compileModel_sound (-1) 1 e w.model m (by norm_num) hp hh
    apply bernParentCheck_sound S m w boxes e.value _ hc
    simpa only [Rat.cast_neg,Rat.cast_one] using hm

theorem compiledBernParentCheck_table (S : ℤ) (e : CellExpr) (w : CellWitness)
    (boxes : List (ℤ×ℤ)) (hc : compiledBernParentCheck S e w boxes=true) :
    TableEncloses S boxes (canonicalControls (qListPoly (gridCoeffs S w)) (-1) 1 (w.coeff.length-1)) := by
  unfold compiledBernParentCheck at hc
  cases hh : compileModel (-1) 1 e w.model with
  | none => simp only [hh,Bool.false_eq_true] at hc
  | some m =>
    rw [hh] at hc
    exact bernParentCheck_table S m w boxes hc

theorem compiled_W_parent_model (terms : ℕ) (z : ℚ) (hz : z≠0)
    (d : SegmentDatum) (dw : DensityWitness) (hd : datumCheck d dw=true)
    (p r : ℚ) (hpoint : 0≤p-|r|) (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ))
    (hp : PositiveSources (WExpr terms z d.segments (p,0) (r,0)))
    (hc : compiledBernParentCheck S (WExpr terms z d.segments (p,0) (r,0)) w boxes=true) :
    ModelsOn (fun t => W (z:ℝ) d.dual.σ (((p:ℝ)+(r:ℝ)*t:ℝ):ℂ))
      ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) (-1) 1 w.remainder := by
  have hm := (compiledBernParentCheck_sound S _ w boxes hp hc).1
  refine ⟨hm.1,hm.2.1,?_⟩
  intro t ht
  have hmul : |(r:ℝ)*t|≤|(r:ℝ)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ht)
  have hnon : (0:ℝ)≤(p:ℝ)+(r:ℝ)*t := by
    have hh : (0:ℝ)≤(p:ℝ)-|(r:ℝ)| := by exact_mod_cast hpoint
    linarith [neg_abs_le ((r:ℝ)*t)]
  have he := WExpr_value terms z hz d dw hd (p,0) (r,0) t
    (by simpa [cqReal] using hnon) (by simp [cqReal])
  have hpt : cqReal (p,0)+cqReal (r,0)*(t:ℂ)=(((p:ℝ)+(r:ℝ)*t:ℝ):ℂ) := by
    simp [cqReal]
  rw [hpt] at he
  dsimp only
  rw [← he]
  exact hm.2.2 t ht

theorem compiled_atom_parent_model (terms : ℕ) (z : ℚ) (hz : z≠0)
    (d : SegmentDatum) (dw : DensityWitness) (hd : datumCheck d dw=true)
    (p r : ℚ) (hpoint : 1≤p-|r| ∧ p+|r|≤4)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ))
    (hp : PositiveSources (atomExpr terms z d.segments p r))
    (hc : compiledBernParentCheck S (atomExpr terms z d.segments p r) w boxes=true) :
    ModelsOn (fun t => omega (z:ℝ) ((p:ℝ)+(r:ℝ)*t)-
      2*U d.dual.σ (-(((p:ℝ)+(r:ℝ)*t:ℝ):ℂ)))
      ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) (-1) 1 w.remainder := by
  have hm := (compiledBernParentCheck_sound S _ w boxes hp hc).1
  refine ⟨hm.1,hm.2.1,?_⟩
  intro t ht
  have hmul : |(r:ℝ)*t|≤|(r:ℝ)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ht)
  have hdom : (p:ℝ)+(r:ℝ)*t∈Icc 1 4 := by
    have hlo : (1:ℝ)≤(p:ℝ)-|(r:ℝ)| := by exact_mod_cast hpoint.1
    have hhi : (p:ℝ)+|(r:ℝ)|≤4 := by exact_mod_cast hpoint.2
    constructor <;> linarith [neg_abs_le ((r:ℝ)*t),le_abs_self ((r:ℝ)*t)]
  have he := atomExpr_value terms z hz d dw hd p r t hdom
  push_cast at he
  dsimp only
  push_cast
  rw [← he]
  exact hm.2.2 t ht

#print axioms compiledBernParentCheck_sound
#print axioms compiled_W_parent_model
#print axioms compiled_atom_parent_model
end CatalanCore.Li2.DecayCert.LatticeGate
