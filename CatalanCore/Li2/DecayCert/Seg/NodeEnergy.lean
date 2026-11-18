module
public import CatalanCore.Li2.DecayCert.Seg.NodeFree
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.Seg
open CatalanCore.Li2.DecayCert CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential
noncomputable section

variable {CC AC : Type} [ContourProj CC] [AtomProj AC]

def nodeContourRow (cc : List (CC × QBox)) (p : SegmentPlacement) (j : ℕ) :
    Option (QInterval×ℚ) := do
  let parent : CC × QBox ← cc[j]?
  if p.edge ≠ ContourProj.edge parent.1 then none else
    pure (⟨ContourProj.left parent.1,ContourProj.right parent.1⟩,parent.2.1)

def nodeAtomRow (ac : List (AC × AtomOut)) (j : ℕ) : Option (QInterval×ℚ) := do
  let parent : AC × AtomOut ← ac[j]?
  pure (⟨AtomProj.left parent.1,AtomProj.right parent.1⟩,parent.2.lb)

theorem nodeContourRow_sound (z : ℚ) (b : BentInput) (cc : List (CC × QBox))
    (hphys : NodeContourPhysical z b cc)
    (p : SegmentPlacement) (j : ℕ) (r : QInterval×ℚ) (hr : nodeContourRow cc p j=some r) :
    ∀ t ∈ Icc (r.1.left:ℝ) (r.1.right:ℝ),(r.2:ℝ) ≤ W (z:ℝ) b.data.dual.σ
      (cqReal (edgeOrigin b p.edge)+cqReal (edgeDirection b p.edge)*(t:ℂ)) := by
  unfold nodeContourRow at hr
  cases hp : cc[j]? with
  | none => simp [hp] at hr
  | some parent =>
    rw [hp] at hr
    change (if p.edge ≠ ContourProj.edge parent.1 then none else
      some ((⟨ContourProj.left parent.1,ContourProj.right parent.1⟩:QInterval),parent.2.1))=some r at hr
    split_ifs at hr with hedge
    have heq : p.edge=ContourProj.edge parent.1 := not_ne_iff.mp hedge
    cases Option.some.inj hr
    intro t ht
    rw [heq]
    exact (hphys parent (List.mem_of_getElem? hp) t ht).1

theorem nodeAtomRow_sound (z : ℚ) (b : BentInput) (ac : List (AC × AtomOut))
    (hphys : NodeAtomWPhysical z b ac)
    (j : ℕ) (r : QInterval×ℚ) (hr : nodeAtomRow ac j=some r) :
    ∀ t ∈ Icc (r.1.left:ℝ) (r.1.right:ℝ),(r.2:ℝ) ≤ W (z:ℝ) b.data.dual.σ (-(t:ℂ)) := by
  unfold nodeAtomRow at hr
  cases hp : ac[j]? with
  | none => simp [hp] at hr
  | some parent =>
    rw [hp] at hr
    change some ((⟨AtomProj.left parent.1,AtomProj.right parent.1⟩:QInterval),parent.2.lb)=some r at hr
    cases Option.some.inj hr
    intro t ht
    exact (hphys parent (List.mem_of_getElem? hp) t ht).1

theorem nodeEnergyLower_pointwise (z : ℚ) (b : BentInput) (hp : placementCheck b=true)
    (cc : List (CC × QBox)) (ac : List (AC × AtomOut))
    (hcc : NodeContourPhysical z b cc) (hac : NodeAtomWPhysical z b ac)
    (e : EnergyPiece) (s : QSegment)
    (hs : (baseSegments b)[e.segment]?=some s) (L : ℚ) (hc : nodeEnergyLower b cc ac e=some L) :
    ∀ x ∈ Icc (e.left.x:ℝ) (e.right.x:ℝ),(L:ℝ) ≤ W (z:ℝ) b.data.dual.σ
      (cqReal s.mid+cqReal s.half*(x:ℂ)) := by
  unfold nodeEnergyLower at hc
  rw [hs] at hc
  change (if e.parents=[] then none else if e.segment < b.upper.length then
      (b.placements[e.segment]? >>= fun p =>
        (e.parents.mapM (nodeContourRow cc p) >>= fun rows =>
          clippedParentLower (min ((p.left+p.right)/2+(p.right-p.left)*e.left.x/2)
              ((p.left+p.right)/2+(p.right-p.left)*e.right.x/2))
            (max ((p.left+p.right)/2+(p.right-p.left)*e.left.x/2)
              ((p.left+p.right)/2+(p.right-p.left)*e.right.x/2)) rows))
    else (e.parents.mapM (nodeAtomRow ac) >>= fun rows =>
      clippedParentLower (min (-s.mid.1-s.half.1*e.left.x) (-s.mid.1-s.half.1*e.right.x))
        (max (-s.mid.1-s.half.1*e.left.x) (-s.mid.1-s.half.1*e.right.x)) rows))=some L at hc
  split_ifs at hc with hnil hupper
  · cases hpget : b.placements[e.segment]? with
    | none => simp [hpget] at hc
    | some p =>
      rw [hpget] at hc
      let tQ : ℚ → ℚ := fun x => (p.left+p.right)/2+(p.right-p.left)*x/2
      let tR : ℝ → ℝ := fun x => ((p.left:ℝ)+(p.right:ℝ))/2+((p.right:ℝ)-(p.left:ℝ))/2*x
      change (e.parents.mapM (nodeContourRow cc p) >>= fun rows =>
        clippedParentLower (min (tQ e.left.x) (tQ e.right.x)) (max (tQ e.left.x) (tQ e.right.x)) rows)=some L at hc
      cases hrows : e.parents.mapM (nodeContourRow cc p) with
      | none => simp [hrows] at hc
      | some rows =>
        simp only [hrows,Option.bind_some] at hc
        have hparents : ∀ r ∈ rows,∀ y ∈ Icc (r.1.left:ℝ) (r.1.right:ℝ),(r.2:ℝ) ≤
            W (z:ℝ) b.data.dual.σ (cqReal (edgeOrigin b p.edge)+cqReal (edgeDirection b p.edge)*(y:ℂ)) := by
          intro r hr
          rcases option_mapM_member e.parents (nodeContourRow cc p) rows hrows r hr with ⟨j,hj,hjr⟩
          exact nodeContourRow_sound z b cc hcc p j r hjr
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
  · cases hrows : e.parents.mapM (nodeAtomRow ac) with
    | none => simp [hrows] at hc
    | some rows =>
      simp only [hrows,Option.bind_some] at hc
      have hparents : ∀ r ∈ rows,∀ y ∈ Icc (r.1.left:ℝ) (r.1.right:ℝ),(r.2:ℝ) ≤ W (z:ℝ) b.data.dual.σ (-(y:ℂ)) := by
        intro r hr
        rcases option_mapM_member e.parents (nodeAtomRow ac) rows hrows r hr with ⟨j,hj,hjr⟩
        exact nodeAtomRow_sound z b ac hac j r hjr
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

theorem nodeEnergyLower_sound (z : ℚ) (b : BentInput) (hp : placementCheck b=true)
    (cc : List (CC × QBox)) (ac : List (AC × AtomOut))
    (hcc : NodeContourPhysical z b cc) (hac : NodeAtomWPhysical z b ac)
    (e : EnergyPiece) (hseg : e.segment < (baseSegments b).length)
    (L : ℚ) (hc : nodeEnergyLower b cc ac e=some L) :
    let s := (baseSegments b)[e.segment]
    ∀ᵐ x : ℝ ∂s.parameterMeasure.restrict (Icc (e.left.x:ℝ) (e.right.x:ℝ)),
      (L:ℝ) ≤ W (z:ℝ) b.data.dual.σ (cqReal s.mid+cqReal s.half*(x:ℂ)) := by
  let s := (baseSegments b)[e.segment]
  have hs : (baseSegments b)[e.segment]?=some s := List.getElem?_eq_getElem hseg
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall (fun x hx => nodeEnergyLower_pointwise z b hp cc ac hcc hac e s hs L hc x hx)

def nodeEnergyRow (b : BentInput) (c : NodeCert CC AC) (e : EnergyPiece) : Option SE := do
  let s ← (baseSegments b)[e.segment]?
  let lo ← nodeEnergyLower b c.contour c.atoms e
  pure (seScale ((if e.segment < b.upper.length then 2 else 1)*lo)
    (arcMassExpr e.terms s e.left e.right))

def nodeEnergyLow (b : BentInput) (c : NodeCert CC AC) (e : EnergyPiece) : ℚ :=
  (nodeEnergyLower b c.contour c.atoms e).getD 0

def nodeEnergyValue (b : BentInput) (c : NodeCert CC AC) (e : EnergyPiece) : ℝ :=
  ((baseSegments b)[e.segment]?.map (fun s => (if e.segment < b.upper.length then (2:ℝ) else 1)*
    (nodeEnergyLow b c e:ℝ)*s.parameterMeasure.real (Icc (e.left.x:ℝ) (e.right.x:ℝ)))).getD 0

theorem nodeEnergyRow_lower (b : BentInput) (c : NodeCert CC AC) (e : EnergyPiece)
    (v : SE) (hv : nodeEnergyRow b c e=some v) :
    nodeEnergyLower b c.contour c.atoms e=some (nodeEnergyLow b c e) := by
  unfold nodeEnergyRow at hv
  cases hs : (baseSegments b)[e.segment]? with
  | none => simp [hs] at hv
  | some s =>
    rw [hs] at hv
    cases hl : nodeEnergyLower b c.contour c.atoms e with
    | none => simp [hl] at hv
    | some L => simp only [nodeEnergyLow,hl,Option.getD_some]

theorem nodeEnergyRow_value (b : BentInput) (c : NodeCert CC AC)
    (hd : datumCheck b.data c.density=true) (hc : energyCoverCheck b c.energyCells=true)
    (e : EnergyPiece) (he : e ∈ c.energyCells) (v : SE) (hv : nodeEnergyRow b c e=some v) :
    v.value=nodeEnergyValue b c e := by
  have hp := energyCoverCheck_piece b c.energyCells hc e he
  let s := (baseSegments b)[e.segment]
  have hs : (baseSegments b)[e.segment]?=some s := List.getElem?_eq_getElem hp.1
  have hL := nodeEnergyRow_lower b c e v hv
  unfold nodeEnergyRow at hv
  rw [hs,hL] at hv
  change some (seScale ((if e.segment < b.upper.length then 2 else 1)*nodeEnergyLow b c e)
    (arcMassExpr e.terms s e.left e.right))=some v at hv
  rw [← Option.some.inj hv,seScale_value]
  have hpos := baseSegments_positive b c.density hd s (List.getElem_mem _)
  have hhalf : cqReal s.half ≠ 0 := by
    rcases (sourceDataCheck_parts b.data.segments b.data.radius c.density hd).2 s
      (baseSegments_mem_data b s (List.getElem_mem _)) with ⟨t,ht,hbern⟩
    exact half_ne_of_cqSq_ne s.half ht.1
  rw [arcMassExpr_parameter e.terms s e.left e.right hhalf hpos hp.2.1 hp.2.2.1 hp.2.2.2.le]
  simp only [nodeEnergyValue,hs,Option.map_some,Option.getD_some,Rat.cast_mul]
  split_ifs <;> norm_num

theorem nodeEnergyRows_lower (z : ℚ) (b : BentInput) (c : NodeCert CC AC)
    (hp : placementCheck b=true) (hcc : NodeContourPhysical z b c.contour)
    (hac : NodeAtomWPhysical z b c.atoms)
    (hc : energyCoverCheck b c.energyCells=true) (vs : List SE)
    (hm : c.energyCells.mapM (nodeEnergyRow b c)=some vs)
    (i : Fin c.energyCells.length) (j : Fin (baseSegments b).length)
    (hlabel : (c.energyCells[i]).segment=j.val) :
    ∀ᵐ x : ℝ ∂((baseSegments b)[j]).parameterMeasure.restrict
      (Icc ((c.energyCells[i]).left.x:ℝ) ((c.energyCells[i]).right.x:ℝ)),
      (nodeEnergyLow b c c.energyCells[i]:ℝ) ≤ W (z:ℝ) b.data.dual.σ
        (cqReal ((baseSegments b)[j]).mid+cqReal ((baseSegments b)[j]).half*(x:ℂ)) := by
  have hei : c.energyCells[i] ∈ c.energyCells := List.getElem_mem _
  have hpiece := energyCoverCheck_piece b c.energyCells hc c.energyCells[i] hei
  rcases option_mapM_input c.energyCells (nodeEnergyRow b c) vs hm c.energyCells[i] hei with ⟨v,hv⟩
  have hL := nodeEnergyRow_lower b c c.energyCells[i] v hv
  have hl := nodeEnergyLower_sound z b hp c.contour c.atoms hcc hac c.energyCells[i] hpiece.1 _ hL
  have hidx : (baseSegments b)[(c.energyCells[i]).segment]'hpiece.1=(baseSegments b)[j] := by
    have hfin : (⟨(c.energyCells[i]).segment,hpiece.1⟩:Fin (baseSegments b).length)=j := Fin.ext hlabel
    exact congrArg (fun k : Fin (baseSegments b).length => (baseSegments b)[k]) hfin
  change ∀ᵐ x : ℝ ∂((baseSegments b)[(c.energyCells[i]).segment]).parameterMeasure.restrict
      (Icc ((c.energyCells[i]).left.x:ℝ) ((c.energyCells[i]).right.x:ℝ)),_ at hl
  rw [hidx] at hl
  exact hl

def nodeEnergyLowAt (b : BentInput) (c : NodeCert CC AC) (i : ℕ) : ℚ :=
  (c.energyCells[i]?.map (nodeEnergyLow b c)).getD 0

theorem nodeEnergyLowAt_get (b : BentInput) (c : NodeCert CC AC) (i : Fin c.energyCells.length) :
    nodeEnergyLowAt b c i.val=nodeEnergyLow b c c.energyCells[i] := by
  simp only [nodeEnergyLowAt,List.getElem?_eq_getElem i.isLt,Option.map_some,Option.getD_some,Fin.getElem_fin]

theorem nodeEnergyRows_sum (b : BentInput) (c : NodeCert CC AC)
    (hd : datumCheck b.data c.density=true) (hc : energyCoverCheck b c.energyCells=true)
    (vs : List SE) (hm : c.energyCells.mapM (nodeEnergyRow b c)=some vs) :
    (vs.map ScalarExpr.value).sum=
      ∑ j : Fin (baseSegments b).length,(if j.val < b.upper.length then (2:ℝ) else 1)*
        ∑ i : Fin c.energyCells.length,if (c.energyCells[i]).segment=j.val then
          (nodeEnergyLowAt b c i.val:ℝ)*((baseSegments b)[j]).parameterMeasure.real
            (Icc ((c.energyCells[i]).left.x:ℝ) ((c.energyCells[i]).right.x:ℝ)) else 0 := by
  rw [option_mapM_sum_values c.energyCells (nodeEnergyRow b c) (nodeEnergyValue b c) vs
    (fun e he => nodeEnergyRow_value b c hd hc e he) hm]
  rw [← fin_sum_list_map c.energyCells (nodeEnergyValue b c)]
  let label : Fin c.energyCells.length → ℕ := fun i => (c.energyCells[i]).segment
  have hlabel (i : Fin c.energyCells.length) : label i < (baseSegments b).length :=
    (energyCoverCheck_piece b c.energyCells hc c.energyCells[i] (List.getElem_mem _)).1
  let weight : Fin (baseSegments b).length → ℝ := fun j => if j.val < b.upper.length then 2 else 1
  let f : Fin (baseSegments b).length → Fin c.energyCells.length → ℝ := fun j i =>
    (nodeEnergyLowAt b c i.val:ℝ)*((baseSegments b)[j]).parameterMeasure.real
      (Icc ((c.energyCells[i]).left.x:ℝ) ((c.energyCells[i]).right.x:ℝ))
  calc
    _ = ∑ i : Fin c.energyCells.length,weight ⟨label i,hlabel i⟩*f ⟨label i,hlabel i⟩ i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [nodeEnergyValue,weight,f,label,nodeEnergyLowAt_get,Fin.getElem_fin]
      have hseg : (c.energyCells[i.val]).segment < (baseSegments b).length := by
        simpa only [label,Fin.getElem_fin] using hlabel i
      rw [List.getElem?_eq_getElem hseg]
      simp only [Option.map_some,Option.getD_some]
      ring
    _ = _ := labelled_sum_reindex label hlabel weight f

theorem nodeEnergyExpr_upper (z : ℚ) (hn : z < 0) (b : BentInput) (c : NodeCert CC AC)
    (hd : datumCheck b.data c.density=true) (hp : placementCheck b=true)
    (hcc : NodeContourPhysical z b c.contour) (hac : NodeAtomWPhysical z b c.atoms)
    (hc : energyCoverCheck b c.energyCells=true) (e : SE) (he : nodeEnergyExpr z b c=some e) :
    I b.data.dual.σ ≤ e.value := by
  have hform : nodeEnergyExpr z b c=(do
    let VI ← bentVExpr z b c.toBent
    let lows ← c.energyCells.mapM (nodeEnergyRow b c)
    pure (seScale (1/2) (seSub VI (seSum lows)))) := rfl
  rw [hform] at he
  cases hv : bentVExpr z b c.toBent with
  | none => simp [hv] at he
  | some VI =>
    rw [hv] at he
    cases hm : c.energyCells.mapM (nodeEnergyRow b c) with
    | none => simp [hm] at he
    | some lows =>
      rw [hm] at he
      change some (seScale (1/2) (seSub VI (seSum lows)))=some e at he
      rw [← Option.some.inj he,seScale_value,seSub_value,seSum_value,bentVExpr_value z hn b c.toBent hd hp VI hv]
      have hl (i : Fin c.energyCells.length) (j : Fin (baseSegments b).length)
          (hlabel : (c.energyCells[i]).segment=j.val) :
          ∀ᵐ x : ℝ ∂((baseSegments b)[j]).parameterMeasure.restrict
            (Icc ((c.energyCells[i]).left.x:ℝ) ((c.energyCells[i]).right.x:ℝ)),
          (nodeEnergyLowAt b c i.val:ℝ) ≤ W (z:ℝ) b.data.dual.σ
            (cqReal ((baseSegments b)[j]).mid+cqReal ((baseSegments b)[j]).half*(x:ℂ)) := by
        rw [nodeEnergyLowAt_get]
        exact nodeEnergyRows_lower z b c hp hcc hac hc lows hm i j hlabel
      have hb := energy_up_bent_labelled z b c.density hd hp c.energyCells hc (nodeEnergyLowAt b c) hl
        (datum_V_integrable (z:ℝ) b.data.dual) (datum_U_integrable b.data.dual)
      rw [← nodeEnergyRows_sum b c hd hc lows hm] at hb
      convert hb using 1 <;> push_cast <;> ring
#print axioms nodeEnergyLower_sound
#print axioms nodeEnergyExpr_upper
end
end CatalanCore.Li2.DecayCert.Seg
