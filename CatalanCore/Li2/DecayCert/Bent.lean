module
public import CatalanCore.Li2.DecayCert.Bent.Free
public import CatalanCore.Li2.DecayCert.Bent.Energy
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem bentSegmentCheck_parts (z : ℚ) (b : BentInput) (c : BentCert)
    (hc : bentSegmentCheck z b c=true) :
    (-1 < z ∧ z < 0 ∧ c.atomCaps.length=b.atoms.length) ∧
    datumCheck b.data c.density=true ∧ placementCheck b=true ∧
    contourCoverCheck b c.contour=true ∧
    (∀ cell ∈ c.contour,∃ B,contourBounds z b cell=some B ∧ B.2 ≤ c.ell) ∧
    atomCoverCheck z b.data c.atoms=true ∧ energyCoverCheck b c.energyCells=true ∧
    scalarUpperCheck (bentTailExpr b c) c.ell=true ∧
    ∃ e,bentEnergyExpr z b c=some e ∧ scalarUpperCheck e c.Iup=true := by
  have h := hc
  simp only [bentSegmentCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape,hatoms⟩,hd⟩,hp⟩,hcover⟩,hbounds⟩,hatomcover⟩,henergycover⟩,htail⟩,henergy⟩
  refine ⟨hshape,hd,hp,hcover,?_,hatomcover,henergycover,htail,?_⟩
  · intro cell hcell
    have hrow := (List.all_eq_true.mp hbounds) cell hcell
    cases hB : contourBounds z b cell with
    | none => simp [hB] at hrow
    | some B =>
      refine ⟨B,rfl,?_⟩
      exact of_decide_eq_true (by simpa only [hB] using hrow)
  · cases he : bentEnergyExpr z b c with
    | none => simp [he] at henergy
    | some e => exact ⟨e,rfl,by simpa only [he] using henergy⟩

theorem bentSegmentCheck_sound (z : ℚ) (b : BentInput) (c : BentCert)
    (hc : bentSegmentCheck z b c=true) :
    FreeBound (z:ℝ) b.geom.frame b.data.dual c.ell ∧ I b.data.dual.σ ≤ (c.Iup:ℝ) := by
  rcases bentSegmentCheck_parts z b c hc with ⟨hshape,hd,hp,hcover,hbounds,hatomcover,henergycover,htail,e,he,hscalar⟩
  have hz : ValidZ (z:ℝ) := by
    have hn : (z:ℝ) < 0 := by exact_mod_cast hshape.2.1
    have hl : (-1:ℝ) < (z:ℝ) := by exact_mod_cast hshape.1
    constructor
    · exact abs_pos.mpr hn.ne
    · rw [abs_of_neg hn]
      linarith
  refine ⟨bent_free_bound z hz hshape.2.1 b c hd hp hcover hbounds htail,?_⟩
  exact (bentEnergyExpr_upper z hshape.2.1 b c hd hp henergycover e he).trans
    (scalarUpperCheck_sound e c.Iup hscalar)
#print axioms bentSegmentCheck_parts
#print axioms bentSegmentCheck_sound
end
end CatalanCore.Li2.DecayCert
