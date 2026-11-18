module
public import CatalanCore.Li2.DecayCert.Covers.Placement
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

def contourParentRow (z : ℚ) (b : BentInput) (cc : List ContourCell) (p : SegmentPlacement) (j : ℕ) :
    Option (QInterval×ℚ) := do
  let parent ← cc[j]?
  if p.edge ≠ parent.edge then none else
    let B ← contourBounds z b parent
    pure (⟨parent.left,parent.right⟩,B.1)

def atomParentRow (z : ℚ) (b : BentInput) (ac : List AtomCell) (j : ℕ) : Option (QInterval×ℚ) := do
  let parent ← ac[j]?
  if atomCellCheck z b.data parent=false then none else
    pure (⟨parent.left,parent.right⟩,parent.witness.cell.lb)

theorem contourParentRow_sound (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true) (cc : List ContourCell)
    (p : SegmentPlacement) (j : ℕ) (r : QInterval×ℚ) (hr : contourParentRow z b cc p j=some r) :
    ∀ t ∈ Icc (r.1.left:ℝ) (r.1.right:ℝ),(r.2:ℝ) ≤ W (z:ℝ) b.data.dual.σ
      (cqReal (edgeOrigin b p.edge)+cqReal (edgeDirection b p.edge)*(t:ℂ)) := by
  unfold contourParentRow at hr
  cases hp : cc[j]? with
  | none => simp [hp] at hr
  | some parent =>
    rw [hp] at hr
    change (if p.edge ≠ parent.edge then none else (contourBounds z b parent >>= fun B =>
      some ((⟨parent.left,parent.right⟩:QInterval),B.1)))=some r at hr
    split_ifs at hr with hedge
    have heq : p.edge=parent.edge := not_ne_iff.mp hedge
    cases hB : contourBounds z b parent with
    | none => simp [hB] at hr
    | some B =>
      simp only [hB,Option.bind_some] at hr
      cases Option.some.inj hr
      intro t ht
      rw [heq]
      exact (contourBounds_physical z hz b dw hd parent B hB t ht).1

theorem atomParentRow_sound (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true) (ac : List AtomCell)
    (j : ℕ) (r : QInterval×ℚ) (hr : atomParentRow z b ac j=some r) :
    ∀ t ∈ Icc (r.1.left:ℝ) (r.1.right:ℝ),(r.2:ℝ) ≤ W (z:ℝ) b.data.dual.σ (-(t:ℂ)) := by
  unfold atomParentRow at hr
  cases hp : ac[j]? with
  | none => simp [hp] at hr
  | some parent =>
    rw [hp] at hr
    change (if atomCellCheck z b.data parent=false then none else
      some ((⟨parent.left,parent.right⟩:QInterval),parent.witness.cell.lb))=some r at hr
    split_ifs at hr with hbad
    have hc : atomCellCheck z b.data parent=true := by cases h : atomCellCheck z b.data parent <;> simp_all
    cases Option.some.inj hr
    intro t ht
    exact (atomCell_W_physical z hz b.data dw hd parent hc t ht).1

theorem energyLower_pointwise (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true) (hp : placementCheck b=true)
    (cc : List ContourCell) (ac : List AtomCell) (e : EnergyPiece) (s : QSegment)
    (hs : (baseSegments b)[e.segment]?=some s) (L : ℚ) (hc : energyLower z b cc ac e=some L) :
    ∀ x ∈ Icc (e.left.x:ℝ) (e.right.x:ℝ),(L:ℝ) ≤ W (z:ℝ) b.data.dual.σ
      (cqReal s.mid+cqReal s.half*(x:ℂ)) := by
  unfold energyLower at hc
  rw [hs] at hc
  change (if e.parents=[] then none else if e.segment < b.upper.length then
      (b.placements[e.segment]? >>= fun p =>
        (e.parents.mapM (contourParentRow z b cc p) >>= fun rows =>
          clippedParentLower (min ((p.left+p.right)/2+(p.right-p.left)*e.left.x/2)
              ((p.left+p.right)/2+(p.right-p.left)*e.right.x/2))
            (max ((p.left+p.right)/2+(p.right-p.left)*e.left.x/2)
              ((p.left+p.right)/2+(p.right-p.left)*e.right.x/2)) rows))
    else (e.parents.mapM (atomParentRow z b ac) >>= fun rows =>
      clippedParentLower (min (-s.mid.1-s.half.1*e.left.x) (-s.mid.1-s.half.1*e.right.x))
        (max (-s.mid.1-s.half.1*e.left.x) (-s.mid.1-s.half.1*e.right.x)) rows))=some L at hc
  split_ifs at hc with hnil hupper
  · cases hpget : b.placements[e.segment]? with
    | none => simp [hpget] at hc
    | some p =>
      rw [hpget] at hc
      let tQ : ℚ → ℚ := fun x => (p.left+p.right)/2+(p.right-p.left)*x/2
      let tR : ℝ → ℝ := fun x => ((p.left:ℝ)+(p.right:ℝ))/2+((p.right:ℝ)-(p.left:ℝ))/2*x
      change (e.parents.mapM (contourParentRow z b cc p) >>= fun rows =>
        clippedParentLower (min (tQ e.left.x) (tQ e.right.x)) (max (tQ e.left.x) (tQ e.right.x)) rows)=some L at hc
      cases hrows : e.parents.mapM (contourParentRow z b cc p) with
      | none => simp [hrows] at hc
      | some rows =>
        simp only [hrows,Option.bind_some] at hc
        have hparents : ∀ r ∈ rows,∀ y ∈ Icc (r.1.left:ℝ) (r.1.right:ℝ),(r.2:ℝ) ≤
            W (z:ℝ) b.data.dual.σ (cqReal (edgeOrigin b p.edge)+cqReal (edgeDirection b p.edge)*(y:ℂ)) := by
          intro r hr
          rcases option_mapM_member e.parents (contourParentRow z b cc p) rows hrows r hr with ⟨j,hj,hjr⟩
          exact contourParentRow_sound z hz b dw hd cc p j r hjr
        have hclip := clippedParentLower_pointwise _ _ _ L rows hparents hc
        have hsup : b.upper[e.segment]?=some s := by
          rw [baseSegments,List.getElem?_append_left hupper] at hs
          exact hs
        have hplace := placementCheck_upper_row b hp e.segment hupper s p hsup hpget
        have htcast (a : ℚ) : (tQ a:ℝ)=tR a := by dsimp only [tQ,tR]; push_cast; ring
        intro x hx
        have htx : tR x ∈ Icc ((min (tQ e.left.x) (tQ e.right.x):ℚ):ℝ)
            ((max (tQ e.left.x) (tQ e.right.x):ℚ):ℝ) := by
          rw [Rat.cast_min,Rat.cast_max,htcast,htcast]
          exact real_affine_mem_between _ _ x _ _ hx
        have hlower := hclip (tR x) htx
        have hpoint : cqReal s.mid+cqReal s.half*(x:ℂ)=cqReal (edgeOrigin b p.edge)+
            cqReal (edgeDirection b p.edge)*(tR x:ℂ) := by
          have h := placement_source_point b s p hplace.2.2.2.2.1 hplace.2.2.2.2.2 x
          convert h using 1 <;> dsimp only [tR] <;> push_cast <;> ring
        rwa [hpoint]
  · cases hrows : e.parents.mapM (atomParentRow z b ac) with
    | none => simp [hrows] at hc
    | some rows =>
      simp only [hrows,Option.bind_some] at hc
      have hparents : ∀ r ∈ rows,∀ y ∈ Icc (r.1.left:ℝ) (r.1.right:ℝ),(r.2:ℝ) ≤ W (z:ℝ) b.data.dual.σ (-(y:ℂ)) := by
        intro r hr
        rcases option_mapM_member e.parents (atomParentRow z b ac) rows hrows r hr with ⟨j,hj,hjr⟩
        exact atomParentRow_sound z hz b dw hd ac j r hjr
      have hclip := clippedParentLower_pointwise _ _ _ L rows hparents hc
      have hsat : s ∈ b.atoms := by
        rw [baseSegments,List.getElem?_append_right (by omega)] at hs
        exact List.mem_of_getElem? hs
      have hatom := placementCheck_atom b hp s hsat
      intro x hx
      have htx : -(s.mid.1:ℝ)-(s.half.1:ℝ)*x ∈
          Icc ((min (-s.mid.1-s.half.1*e.left.x) (-s.mid.1-s.half.1*e.right.x):ℚ):ℝ)
            ((max (-s.mid.1-s.half.1*e.left.x) (-s.mid.1-s.half.1*e.right.x):ℚ):ℝ) := by
        push_cast
        simpa only [sub_eq_add_neg,neg_mul] using real_affine_mem_between (-(s.mid.1:ℝ)) (-(s.half.1:ℝ)) x _ _ hx
      have hlower := hclip (-(s.mid.1:ℝ)-(s.half.1:ℝ)*x) htx
      rw [atom_source_point s hatom.1 hatom.2.1 x]
      exact hlower

theorem energyLower_sound (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (hp : placementCheck b=true) (cc : List ContourCell) (ac : List AtomCell)
    (e : EnergyPiece) (hseg : e.segment < (baseSegments b).length)
    (L : ℚ) (hc : energyLower z b cc ac e=some L) :
    let s := (baseSegments b)[e.segment]
    ∀ᵐ x : ℝ ∂s.parameterMeasure.restrict (Icc (e.left.x:ℝ) (e.right.x:ℝ)),
      (L:ℝ) ≤ W (z:ℝ) b.data.dual.σ (cqReal s.mid+cqReal s.half*(x:ℂ)) := by
  let s := (baseSegments b)[e.segment]
  have hs : (baseSegments b)[e.segment]?=some s := List.getElem?_eq_getElem hseg
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall (fun x hx => energyLower_pointwise z hz b dw hd hp cc ac e s hs L hc x hx)
#print axioms contourParentRow_sound
#print axioms atomParentRow_sound
#print axioms energyLower_pointwise
#print axioms energyLower_sound
end
end CatalanCore.Li2.DecayCert
