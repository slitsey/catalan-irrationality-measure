module
public import CatalanCore.Li2.DecayCert.Holder.CopySound
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem option_mapM_sum_bounds {α : Type*} (xs : List α) (f : α → Option QBox) (g : α → ℝ) :
    ∀ bs : List QBox,
    (∀ a ∈ xs,∀ b,f a=some b → g a ∈ Icc (b.1:ℝ) (b.2:ℝ)) → xs.mapM f=some bs →
    (((bs.map Prod.fst).sum:ℚ):ℝ) ≤ (xs.map g).sum ∧
      (xs.map g).sum ≤ (((bs.map Prod.snd).sum:ℚ):ℝ) := by
  induction xs with
  | nil =>
    intro bs hf hm
    have he : ([]:List QBox)=bs := Option.some.inj hm
    subst bs
    simp
  | cons a xs ih =>
    intro bs hf hm
    cases ha : f a with
    | none => simp [ha] at hm
    | some b =>
      cases ht : xs.mapM f with
      | none => simp [ha,ht] at hm
      | some cs =>
        simp only [List.mapM_cons,ha,ht,Option.bind_some,Option.pure_def] at hm
        cases Option.some.inj hm
        have hhead := hf a List.mem_cons_self b ha
        have htail := ih cs (fun q hq => hf q (List.mem_cons_of_mem a hq)) ht
        simp only [List.map_cons,List.sum_cons,Rat.cast_add]
        exact ⟨add_le_add hhead.1 htail.1,add_le_add hhead.2 htail.2⟩

theorem map_range_option_getD {α β : Type*} (xs : List α) (f : α → β) (d : β) :
    (List.range xs.length).map (fun j => (xs[j]?.map f).getD d)=xs.map f := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hi0 : i < xs.length := by simpa using hi'
  simp [List.getElem?_eq_getElem hi0]

def holderPointBounds (d : SegmentDatum) (c : NodeCell) (w : HolderCellWitness) (j : ℕ) : Option QBox := do
  let s ← d.segments[j]?
  let p ← w.points[j]?
  let h ← w.copies[j]?
  if cellUBF (endpointCell c (.segment s c.p c.e)) p=false then none else
    let H ← holderCopyBound s c.p c.e c.width h
    pure (p.lb-H,p.ub+H)

theorem holderPointBounds_sound (d : SegmentDatum) (dw : DensityWitness) (hd : datumCheck d dw=true)
    (c : NodeCell) (w : HolderCellWitness) (j : ℕ) (B : QBox)
    (hb : holderPointBounds d c w j=some B) :
    ∀ u ∈ Icc 0 (c.width:ℝ),
      ((d.segments[j]?.map (fun s => P s.measure (cqReal c.p+cqReal c.e*(u:ℂ)))).getD 0) ∈ Icc (B.1:ℝ) (B.2:ℝ) := by
  unfold holderPointBounds at hb
  cases hs : d.segments[j]? with
  | none => simp [hs] at hb
  | some s =>
    cases hp : w.points[j]? with
    | none => simp [hs,hp] at hb
    | some p =>
      cases hh : w.copies[j]? with
      | none => simp [hs,hp,hh] at hb
      | some h =>
        rw [hs,hp,hh] at hb
        change (if cellUBF (endpointCell c (.segment s c.p c.e)) p=false then none else
          (holderCopyBound s c.p c.e c.width h >>= fun H => some (p.lb-H,p.ub+H)))=some B at hb
        split_ifs at hb with hbad
        have hpoint : cellUBF (endpointCell c (.segment s c.p c.e)) p=true := by
          cases hval : cellUBF (endpointCell c (.segment s c.p c.e)) p <;> simp_all
        cases hH : holderCopyBound s c.p c.e c.width h with
        | none => simp [hH] at hb
        | some H =>
          simp only [hH,Option.bind_some,Option.pure_def] at hb
          cases Option.some.inj hb
          have hpos := (datumCheck_positive d dw hd).1 s (List.mem_of_getElem? hs)
          have hp0 := cellUBF_spec (endpointCell c (.segment s c.p c.e)) p hpos hpoint 0 (by simp [endpointCell])
          change (CellExpr.segment s c.p c.e).value 0 ∈ Icc (p.lb:ℝ) (p.ub:ℝ) at hp0
          simp only [CellExpr.value,Complex.ofReal_zero,mul_zero,add_zero] at hp0
          intro u hu
          have hdif := abs_le.mp (holderCopyBound_sound s c.p c.e c.width h H hpos hH u hu)
          simp only [hs,Option.map_some,Option.getD_some,Prod.fst,Prod.snd,Rat.cast_sub,Rat.cast_add]
          constructor <;> linarith [hp0.1,hp0.2]

theorem holderCellBounds_shape (z : ℚ) (d : SegmentDatum) (c : NodeCell) (w : HolderCellWitness) (B : QBox)
    (hb : holderCellBounds z d c w=some B) :
    ∃ bs : List QBox,0 < c.width ∧
      cellUBF (makeCell c (fieldExpr c.terms z c.p c.e)) w.field=true ∧
      (List.range d.segments.length).mapM (holderPointBounds d c w)=some bs ∧
      B=(w.field.lb+2*(bs.map Prod.fst).sum,w.field.ub+2*(bs.map Prod.snd).sum) := by
  unfold holderCellBounds at hb
  split at hb
  · contradiction
  · rename_i hwidth
    push_neg at hwidth
    split at hb
    · contradiction
    · rename_i hfield
      have hf : cellUBF (makeCell c (fieldExpr c.terms z c.p c.e)) w.field=true := by
        cases hval : cellUBF (makeCell c (fieldExpr c.terms z c.p c.e)) w.field <;> simp_all
      change ((List.range d.segments.length).mapM (holderPointBounds d c w) >>= fun bs =>
        some (w.field.lb+2*(bs.map Prod.fst).sum,w.field.ub+2*(bs.map Prod.snd).sum))=some B at hb
      cases hm : (List.range d.segments.length).mapM (holderPointBounds d c w) with
      | none => simp [hm] at hb
      | some bs =>
        simp only [hm,Option.bind_some] at hb
        exact ⟨bs,hwidth.1,hf,rfl,(Option.some.inj hb).symm⟩

theorem holderCellBounds_sound (z : ℚ) (d : SegmentDatum) (dw : DensityWitness) (hd : datumCheck d dw=true)
    (c : NodeCell) (w : HolderCellWitness) (B : QBox) (hb : holderCellBounds z d c w=some B)
    (hre : ∀ u ∈ Icc 0 (c.width:ℝ),0 ≤ (cqReal c.p+cqReal c.e*(u:ℂ)).re)
    (him : ∀ u ∈ Icc 0 (c.width:ℝ),0 ≤ (cqReal c.p+cqReal c.e*(u:ℂ)).im) :
    ∀ u ∈ Icc 0 (c.width:ℝ),W (z:ℝ) d.dual.σ (cqReal c.p+cqReal c.e*(u:ℂ)) ∈ Icc (B.1:ℝ) (B.2:ℝ) := by
  rcases holderCellBounds_shape z d c w B hb with ⟨bs,hwidth,hfield,hmap,hB⟩
  have hpfield : PositiveSources (fieldExpr c.terms z c.p c.e) := by simp [fieldExpr,exprSum,PositiveSources]
  intro u hu
  let zz := cqReal c.p+cqReal c.e*(u:ℂ)
  have hf := cellUBF_spec (makeCell c (fieldExpr c.terms z c.p c.e)) w.field hpfield hfield u (by simpa [makeCell] using hu)
  change (fieldExpr c.terms z c.p c.e).value u ∈ Icc (w.field.lb:ℝ) (w.field.ub:ℝ) at hf
  rw [fieldExpr_value _ _ _ _ _ (hre u hu) (him u hu)] at hf
  have hs := option_mapM_sum_bounds (List.range d.segments.length) (holderPointBounds d c w)
    (fun j => (d.segments[j]?.map (fun s => P s.measure zz)).getD 0) bs
    (fun j hj b hjb => holderPointBounds_sound d dw hd c w j b hjb u hu) hmap
  rw [map_range_option_getD] at hs
  have hsum : P d.dual.σ zz=(d.segments.map (fun s => P s.measure zz)).sum := by
    rw [d.measure_eq]
    exact checked_sources_P_sum d.segments d.radius dw hd zz
  rw [← hsum] at hs
  rw [hB]
  simp only [Prod.fst,Prod.snd,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat]
  change (w.field.lb:ℝ)+2*(((bs.map Prod.fst).sum:ℚ):ℝ) ≤ V (z:ℝ) zz-2*(-P d.dual.σ zz) ∧
    V (z:ℝ) zz-2*(-P d.dual.σ zz) ≤ (w.field.ub:ℝ)+2*(((bs.map Prod.snd).sum:ℚ):ℝ)
  constructor <;> linarith [hf.1,hf.2,hs.1,hs.2]

theorem fieldCellBounds_sound (z : ℚ) (hz : z ≠ 0) (d : SegmentDatum)
    (dw : DensityWitness) (hd : datumCheck d dw=true) (c : NodeCell)
    (m : FieldMethod) (B : QBox) (hb : fieldCellBounds z d c m=some B)
    (hre : ∀ u ∈ Icc 0 (c.width:ℝ),0 ≤ (cqReal c.p+cqReal c.e*(u:ℂ)).re)
    (him : ∀ u ∈ Icc 0 (c.width:ℝ),0 ≤ (cqReal c.p+cqReal c.e*(u:ℂ)).im) :
    ∀ u ∈ Icc 0 (c.width:ℝ),W (z:ℝ) d.dual.σ (cqReal c.p+cqReal c.e*(u:ℂ)) ∈ Icc (B.1:ℝ) (B.2:ℝ) := by
  cases m with
  | holder w => exact holderCellBounds_sound z d dw hd c w B hb hre him
  | taylor w =>
    dsimp only [fieldCellBounds] at hb
    split_ifs at hb with hg
    cases Option.some.inj hb
    have hp : PositiveSources (WExpr c.terms z d.segments c.p c.e) := by
      unfold WExpr
      constructor
      · simp [fieldExpr,exprSum,PositiveSources]
      · have hpos := (datumCheck_positive d dw hd).1
        have haux : ∀ ss : List QSegment,(∀ s ∈ ss,PositiveSources (.segment s c.p c.e)) →
            PositiveSources (exprSum (ss.map (fun s => .scale 2 (.segment s c.p c.e)))) := by
          intro ss hs
          unfold exprSum
          have hh : ∀ xs : List CellExpr,∀ b : CellExpr,PositiveSources b →
              (∀ e ∈ xs,PositiveSources e) → PositiveSources (xs.foldl CellExpr.add b) := by
            intro xs
            induction xs with
            | nil => simp
            | cons e xs ih => intro b hb hx; exact ih (.add b e) ⟨hb,hx e List.mem_cons_self⟩ (fun q hq => hx q (List.mem_cons_of_mem e hq))
          apply hh (ss.map (fun s => .scale 2 (.segment s c.p c.e))) (.constant (.rat 0)) trivial
          intro e he
          rcases List.mem_map.mp he with ⟨s,hsm,rfl⟩
          exact hs s hsm
        exact haux d.segments hpos
    intro u hu
    have h := cellUBF_spec (makeCell c (WExpr c.terms z d.segments c.p c.e)) w hp hg u (by simpa [makeCell] using hu)
    change (WExpr c.terms z d.segments c.p c.e).value u ∈ Icc (w.lb:ℝ) (w.ub:ℝ) at h
    rwa [WExpr_value _ _ hz d dw hd _ _ _ (hre u hu) (him u hu)] at h
#print axioms option_mapM_sum_bounds
#print axioms map_range_option_getD
#print axioms holderPointBounds_sound
#print axioms holderCellBounds_shape
#print axioms holderCellBounds_sound
#print axioms fieldCellBounds_sound
end
end CatalanCore.Li2.DecayCert
