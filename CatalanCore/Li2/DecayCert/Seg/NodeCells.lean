module
public import CatalanCore.Li2.DecayCert.Seg.Ball
public import CatalanCore.Li2.DecayCert.Seg.NodeDefs
public import CatalanCore.Li2.DecayCert.Covers.Physical
/-! Contour and atom cells of the bent node built from integer segment copies; their soundness
gives the per-cell hypotheses `NodeContourPhysical`, `NodeAtomWPhysical`, `NodeAtomLinePhysical`. -/
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.Seg
open CatalanCore.Li2.DecayCert Polynomial
open CatalanCore.Li2.Decay

/-! ### Integer polynomial models -/

/-- Integer coefficient lists (scale `1/S`), added with padding. -/
def iadd : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | x::a, y::b => (x+y)::iadd a b

def qOf (S : ℤ) (l : List ℤ) : List ℝ := l.map (fun c : ℤ => (((c:ℚ)/S:ℚ):ℝ))

theorem evalModel_nil (u : ℝ) : evalModel [] u=0 := by simp [evalModel]

theorem evalModel_cons (x : ℝ) (a : List ℝ) (u : ℝ) :
    evalModel (x::a) u=x+u*evalModel a u := by
  unfold evalModel
  rw [List.length_cons,Finset.sum_range_succ',Finset.mul_sum]
  simp only [List.getElem!_cons_succ,List.getElem!_cons_zero,pow_zero,mul_one,pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem evalModel_iadd (S : ℤ) (u : ℝ) : ∀ a b : List ℤ,
    evalModel (qOf S (iadd a b)) u=evalModel (qOf S a) u+evalModel (qOf S b) u
  | [], b => by simp [iadd,qOf,evalModel_nil]
  | x::a, [] => by simp [iadd,qOf,evalModel_nil]
  | x::a, y::b => by
    simp only [iadd,qOf,List.map_cons] at *
    rw [evalModel_cons,evalModel_cons,evalModel_cons]
    have := evalModel_iadd S u a b
    simp only [qOf] at this
    rw [this]; push_cast; ring

theorem evalModel_two (S : ℤ) (u : ℝ) : ∀ a : List ℤ,
    evalModel (qOf S (a.map (fun c => 2*c))) u=2*evalModel (qOf S a) u
  | [] => by simp [qOf,evalModel_nil]
  | x::a => by
    simp only [qOf,List.map_cons] at *
    rw [evalModel_cons,evalModel_cons]
    have := evalModel_two S u a
    simp only [qOf] at this
    rw [this]; push_cast; ring

/-- The doubled copies of all segments, summed. -/
def copySum (S : ℤ) (p e : CQ) (rt : ℚ) : List QSegment → List SegSharedI → List CopyI →
    Option (List ℤ×ℤ)
  | [], [], [] => some ([],0)
  | d::ds, s::ss, w::ws => do
      let o ← ballCopyJ S s d p e rt w
      let r ← copySum S p e rt ds ss ws
      pure (iadd (o.1.map (fun c => 2*c)) r.1,2*o.2+r.2)
  | _, _, _ => none

def sharedOK (S : ℤ) : List QSegment → List SegSharedI → Bool
  | [], [] => true
  | d::ds, s::ss => s.ok S d && sharedOK S ds ss
  | _, _ => false

theorem copySum_model (S : ℤ) (hS : 0 < S) (p e : CQ) (rt : ℚ) (hrt : 0 ≤ rt) :
    ∀ (ds : List QSegment) (ss : List SegSharedI) (ws : List CopyI) (r : List ℤ×ℤ),
    sharedOK S ds ss=true →
    (∀ d ∈ ds,∀ x ∈ Set.Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x) →
    copySum S p e rt ds ss ws=some r →
    Models (fun u => (ds.map (fun d => 2*(CellExpr.segment d p e).value u)).sum) (qOf S r.1) rt
      (((r.2:ℚ)/S:ℚ):ℝ) := by
  intro ds
  induction ds with
  | nil =>
    intro ss ws r _ _ h
    rcases ss with _|⟨s,ss⟩ <;> rcases ws with _|⟨w,ws⟩ <;> simp [copySum] at h
    subst h
    refine ⟨by exact_mod_cast hrt,by simp,fun u _ => ?_⟩
    simp [qOf,evalModel_nil]
  | cons d ds ih =>
    intro ss ws r hok hpos h
    rcases ss with _|⟨s,ss⟩ <;> rcases ws with _|⟨w,ws⟩
    · simp [copySum] at h
    · simp [copySum] at h
    · simp [copySum] at h
    simp only [sharedOK,Bool.and_eq_true] at hok
    simp only [copySum] at h
    cases ho : ballCopyJ S s d p e rt w with
    | none => simp [ho] at h
    | some o =>
    cases hr : copySum S p e rt ds ss ws with
    | none => simp [ho,hr] at h
    | some r' =>
    simp only [ho,hr,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.some.injEq] at h
    subst h
    have hm1 := ballCopyJ_model S hS s d hok.1 p e rt w o (hpos d List.mem_cons_self) ho
    have hm2 := ih ss ws r' hok.2 (fun d' hd' => hpos d' (List.mem_cons_of_mem _ hd')) hr
    refine ⟨hm1.1,?_,fun u hu => ?_⟩
    · have a1 := hm1.2.1; have a2 := hm2.2.1
      push_cast at a1 a2 ⊢
      rw [add_div,mul_div_assoc]; linarith
    · have h1 := hm1.2.2 u hu
      have h2 := hm2.2.2 u hu
      rw [evalModel_iadd,evalModel_two]
      simp only [List.map_cons,List.sum_cons]
      have e1 : evalModel (qOf S o.1) u=evalModel (o.1.map (fun c : ℤ => (((c:ℚ)/S:ℚ):ℝ))) u := rfl
      rw [← e1] at h1
      push_cast at h1 h2 ⊢
      rw [add_div,mul_div_assoc]
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]

/-! ### Outward rounding to a dyadic grid -/

def roundDn (G : ℤ) (x : ℚ) : ℚ := ((x.num*G/(x.den:ℤ):ℤ):ℚ)/G
def roundUp (G : ℤ) (x : ℚ) : ℚ := ((cdiv (x.num*G) (x.den:ℤ)):ℚ)/G

theorem roundDn_le (G : ℤ) (hG : 0 < G) (x : ℚ) : roundDn G x ≤ x := floor_scale_le x G hG
theorem le_roundUp (G : ℤ) (hG : 0 < G) (x : ℚ) : x ≤ roundUp G x := cdiv_scale_ge x G hG

/-! ### Contour cells -/

/-- A contour cell: geometry, the field model witness, and one integer copy per segment. -/
structure ContourCellJ where
  edge : ℕ
  left : ℚ
  right : ℚ
  backwards : Bool
  terms : ℕ
  field : CellWitness
  copies : List CopyI

instance : ContourProj ContourCellJ := ⟨ContourCellJ.edge,ContourCellJ.left,ContourCellJ.right⟩

def ContourCellJ.toCell (S : ℤ) (c : ContourCellJ) : ContourCell :=
  ⟨c.edge,c.left,c.right,c.backwards,S,c.terms,.taylor c.field⟩

/-- Integer model of a polynomial plus error: bounds rounded outward to the grid `1/G`. -/
def modelBox (S G : ℤ) (cs : List ℤ) (err width : ℚ) : QBox :=
  let a := cs.map (fun c : ℤ => (c:ℚ)/S)
  (roundDn G (polyLBQ a 0 width-err),roundUp G (polyUBQ a 0 width+err))

/-- The fused field model on `[0,width]` at scale `S`: compile, round, check. -/
noncomputable def fieldModelI (S : ℤ) (x : CellExpr) (width : ℚ) (w : CellWitness) : Bool :=
  match compileModel 0 width x w.model with
  | none => false
  | some m => decide (0 ≤ width) && coefficientCheck S m w && remainderCheck S (max |0| |width|) m w

noncomputable def contourCellJ (S G : ℤ) (z : ℚ) (b : BentInput) (ss : List SegSharedI) (c : ContourCellJ) :
    Option QBox :=
  if c.edge ≤ b.geom.polygon.edges ∧ 0 ≤ c.left ∧ c.left < c.right ∧ c.right ≤ edgeLimit b c.edge then
    let nc := contourNodeCell b (c.toCell S)
    if fieldModelI S (fieldExpr c.terms z nc.p nc.e) nc.width c.field then
      match copySum S nc.p nc.e nc.width b.data.segments ss c.copies with
      | some r => some (modelBox S G (iadd c.field.coeff r.1)
          (c.field.remainder+(r.2:ℚ)/S) nc.width)
      | none => none
    else none
  else none

theorem fieldModelI_sound (S : ℤ) (x : CellExpr) (width : ℚ) (w : CellWitness)
    (hp : PositiveSources x) (hc : fieldModelI S x width w=true) :
    ModelsOn x.value (qOf S w.coeff) 0 width w.remainder := by
  unfold fieldModelI at hc
  split at hc
  · contradiction
  rename_i m hm
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0,hco⟩,hrm⟩ := hc
  have h := roundModel_sound S 0 width m w x.value
    (compileModel_sound 0 width x w.model m (of_decide_eq_true h0) hp hm) hco hrm
  have e : (gridCoeffs S w).map (fun q : ℚ => (q:ℝ))=qOf S w.coeff := by
    simp [gridCoeffs,qOf,List.map_map]
  rw [e] at h
  simpa using h

/-- The bound box of a model, as an enclosure. -/
theorem modelBox_spec (S G : ℤ) (hG : 0 < G) (cs : List ℤ) (err width : ℚ) (f : ℝ → ℝ)
    (hm : ModelsOn f (qOf S cs) 0 width err) :
    ∀ u ∈ Set.Icc (0:ℝ) (width:ℝ),f u ∈ Set.Icc ((modelBox S G cs err width).1:ℝ)
      ((modelBox S G cs err width).2:ℝ) := by
  have e : qOf S cs=(cs.map (fun c : ℤ => (c:ℚ)/S)).map (fun x : ℚ => (x:ℝ)) := by
    simp [qOf,List.map_map]
  rw [e] at hm
  intro u hu
  have hm' : ModelsOn f ((cs.map (fun c : ℤ => (c:ℚ)/S)).map (fun x : ℚ => (x:ℝ)))
      ((0:ℚ):ℝ) (width:ℝ) err := by rw [Rat.cast_zero]; exact hm
  have h := cell_ub_lb f _ 0 width err hm' u (by rw [Rat.cast_zero]; exact hu)
  have h1 : ((roundDn G (polyLBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) 0 width-err):ℚ):ℝ) ≤
      ((polyLBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) 0 width-err:ℚ):ℝ) := Rat.cast_le.mpr (roundDn_le G hG _)
  have h2 : ((polyUBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) 0 width+err:ℚ):ℝ) ≤
      ((roundUp G (polyUBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) 0 width+err):ℚ):ℝ) :=
    Rat.cast_le.mpr (le_roundUp G hG _)
  exact ⟨h1.trans h.1,h.2.trans h2⟩

theorem positive_fieldExpr (terms : ℕ) (z : ℚ) (p e : CQ) : PositiveSources (fieldExpr terms z p e) := by
  simp [fieldExpr,exprSum,PositiveSources]

theorem contourCellJ_sound (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (c : ContourCellJ) (B : QBox) (hc : contourCellJ S G z b ss c=some B) :
    ∀ t ∈ Set.Icc ((ContourProj.left c:ℚ):ℝ) ((ContourProj.right c:ℚ):ℝ),
      W (z:ℝ) b.data.dual.σ (cqReal (edgeOrigin b (ContourProj.edge c))+
        cqReal (edgeDirection b (ContourProj.edge c))*(t:ℂ)) ∈ Set.Icc (B.1:ℝ) (B.2:ℝ) := by
  unfold contourCellJ at hc
  split_ifs at hc with hg
  set cc := c.toCell S
  set nc := contourNodeCell b cc
  cases hr : copySum S nc.p nc.e nc.width b.data.segments ss c.copies with
  | none => simp [hr] at hc
  | some r =>
  simp only [hr] at hc
  split_ifs at hc with hf
  simp only [Option.some.injEq] at hc
  subst hc
  have hw : nc.width=c.right-c.left := rfl
  have hw0 : (0:ℚ) ≤ nc.width := by rw [hw]; linarith [hg.2.2.1]
  -- field and copies, then the sum
  have hF := fieldModelI_sound S _ _ _ (positive_fieldExpr _ _ _ _) hf
  have hpos := (datumCheck_positive b.data dw hd).1
  have hC := copySum_model S hS nc.p nc.e nc.width hw0 _ ss c.copies r hss hpos hr
  have hC' := hC.onIcc 0 nc.width (by exact_mod_cast hw0) (fun u hu => by
    rw [abs_of_nonneg hu.1]; exact hu.2)
  have hsum : ModelsOn (WExpr c.terms z b.data.segments nc.p nc.e).value
      (qOf S (iadd c.field.coeff r.1)) 0 nc.width (((c.field.remainder+(r.2:ℚ)/S):ℚ):ℝ) := by
    refine ⟨by exact_mod_cast hw0,?_,fun u hu => ?_⟩
    · have := hF.2.1; have := hC'.2.1; push_cast at *; linarith
    · have h1 := hF.2.2 u hu
      have h2 := hC'.2.2 u hu
      have hv : (WExpr c.terms z b.data.segments nc.p nc.e).value u=
          (fieldExpr c.terms z nc.p nc.e).value u+
            (b.data.segments.map (fun d => 2*(CellExpr.segment d nc.p nc.e).value u)).sum := by
        change (fieldExpr c.terms z nc.p nc.e).value u+
          (exprSum (b.data.segments.map (fun s => .scale 2 (.segment s nc.p nc.e)))).value u=_
        rw [exprSum_value,List.map_map]
        rfl
      rw [hv,evalModel_iadd]
      push_cast at h1 h2 ⊢
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
  have hbox := modelBox_spec S G hG _ _ _ _ hsum
  -- geometry, as in `cellC1_okF`
  intro t ht
  change t ∈ Set.Icc ((c.left:ℚ):ℝ) ((c.right:ℚ):ℝ) at ht
  let u := if c.backwards then (c.right:ℝ)-t else t-(c.left:ℝ)
  have hu : u ∈ Set.Icc 0 (nc.width:ℝ) := by
    rw [hw]; simp only [Rat.cast_sub]
    cases hb : c.backwards <;> dsimp only [u] <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] <;>
      constructor <;> linarith [ht.1,ht.2]
  have hparam : (if cc.backwards then (cc.right:ℝ)-u else (cc.left:ℝ)+u)=t := by
    change (if c.backwards then (c.right:ℝ)-u else (c.left:ℝ)+u)=t
    cases hb : c.backwards <;> dsimp only [u] <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] <;> ring
  have hpt := contour_cell_parameter b cc u
  rw [hparam] at hpt
  have hquad := bent_edge_quadrant b c.edge hg.1 t ⟨by
      have : (0:ℝ) ≤ (c.left:ℝ) := by exact_mod_cast hg.2.1
      linarith [ht.1],by
      have : (c.right:ℝ) ≤ (edgeLimit b c.edge:ℝ) := by exact_mod_cast hg.2.2.2
      linarith [ht.2]⟩
  have hquad' : 0 ≤ (cqReal nc.p+cqReal nc.e*(u:ℂ)).re ∧ 0 ≤ (cqReal nc.p+cqReal nc.e*(u:ℂ)).im := by
    rw [hpt]; exact hquad
  have hv := hbox u hu
  rw [WExpr_value _ _ hz b.data dw hd _ _ _ hquad'.1 hquad'.2,hpt] at hv
  exact hv

/-- All stored contour cells are sound: the per-cell hypothesis of the node assembly. -/
theorem nodeContourPhysical_of_cells (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0)
    (b : BentInput) (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (cs : List (ContourCellJ × QBox)) (hcs : ∀ x ∈ cs,contourCellJ S G z b ss x.1=some x.2) :
    NodeContourPhysical z b cs :=
  fun x hx => contourCellJ_sound S G hS hG z hz b dw hd ss hss x.1 x.2 (hcs x hx)

/-! ### Atom cells -/

/-- An atom cell on `[left,right] ⊂ [1,4]`: the elementary-part witness and one copy per segment. -/
structure AtomCellJ where
  left : ℚ
  right : ℚ
  backwards : Bool
  terms : ℕ
  field : CellWitness
  copies : List CopyI

instance : AtomProj AtomCellJ := ⟨AtomCellJ.left,AtomCellJ.right⟩

def AtomCellJ.start (c : AtomCellJ) : ℚ := if c.backwards then c.right else c.left
def AtomCellJ.dir (c : AtomCellJ) : ℚ := if c.backwards then -1 else 1

/-- The elementary (non-segment) part of `atomExpr`. -/
def atomElemExpr (terms : ℕ) (z x dir : ℚ) : CellExpr :=
  exprSum [.scale 2 (.xlog x dir), .scale (-3) (.xlog (x-1) dir),
    .scale (-1) (.xlog (4-x) (-dir)),
    .linear (seAdd (.rat 1) (seScale (-x) (.log terms |z|)))
      (seScale (-dir) (.log terms |z|))]

noncomputable def atomCellJ (S G : ℤ) (z : ℚ) (b : BentInput) (ss : List SegSharedI) (c : AtomCellJ) :
    Option AtomOut :=
  if 1 ≤ c.left ∧ c.left < c.right ∧ c.right ≤ 4 then
    let w := c.right-c.left
    if fieldModelI S (atomElemExpr c.terms z c.start c.dir) w c.field then
      match copySum S (-c.start,0) (-c.dir,0) w b.data.segments ss c.copies with
      | some r =>
        let cs := iadd c.field.coeff r.1
        let err := c.field.remainder+(r.2:ℚ)/S
        let bx := modelBox S G cs err w
        let line := upperLine (cs.map (fun c : ℤ => (c:ℚ)/S)) w err
        some ⟨c.backwards,roundUp G line.1,roundUp G line.2,bx.1,bx.2⟩
      | none => none
    else none
  else none

theorem atomCellJ_sound (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (c : AtomCellJ) (o : AtomOut) (hc : atomCellJ S G z b ss c=some o) :
    (∀ t ∈ Set.Icc ((AtomProj.left c:ℚ):ℝ) ((AtomProj.right c:ℚ):ℝ),
      W (z:ℝ) b.data.dual.σ (-(t:ℂ)) ∈ Set.Icc (o.lb:ℝ) (o.ub:ℝ)) ∧
    (∀ u ∈ Set.Icc (0:ℝ) ((AtomProj.right c-AtomProj.left c:ℚ):ℝ),
      omega (z:ℝ) (((o.start (AtomProj.left c) (AtomProj.right c):ℚ):ℝ)+((o.dir:ℚ):ℝ)*u)-
        2*U b.data.dual.σ (-((((o.start (AtomProj.left c) (AtomProj.right c):ℚ):ℝ)+
          ((o.dir:ℚ):ℝ)*u:ℝ):ℂ)) ≤ (o.a:ℝ)+(o.b:ℝ)*u) := by
  unfold atomCellJ at hc
  split_ifs at hc with hg
  set w := c.right-c.left
  cases hr : copySum S (-c.start,0) (-c.dir,0) w b.data.segments ss c.copies with
  | none => simp [hr] at hc
  | some r =>
  simp only [hr] at hc
  split_ifs at hc with hf
  simp only [Option.some.injEq] at hc
  subst hc
  have hw0 : (0:ℚ) ≤ w := by simp only [w]; linarith [hg.2.1]
  have hF := fieldModelI_sound S _ _ _ (by
    apply positiveSources_exprSum; intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> trivial) hf
  have hpos := (datumCheck_positive b.data dw hd).1
  have hC := copySum_model S hS _ _ w hw0 _ ss c.copies r hss hpos hr
  have hC' := hC.onIcc 0 w (by exact_mod_cast hw0) (fun u hu => by
    rw [abs_of_nonneg hu.1]; exact hu.2)
  have hsum : ModelsOn (atomExpr c.terms z b.data.segments c.start c.dir).value
      (qOf S (iadd c.field.coeff r.1)) 0 w (((c.field.remainder+(r.2:ℚ)/S):ℚ):ℝ) := by
    refine ⟨by exact_mod_cast hw0,?_,fun u hu => ?_⟩
    · have := hF.2.1; have := hC'.2.1; push_cast at *; linarith
    · have h1 := hF.2.2 u hu
      have h2 := hC'.2.2 u hu
      have hv : (atomExpr c.terms z b.data.segments c.start c.dir).value u=
          (atomElemExpr c.terms z c.start c.dir).value u+
            (b.data.segments.map (fun d => 2*(CellExpr.segment d (-c.start,0) (-c.dir,0)).value u)).sum := by
        have h0 : (atomExpr c.terms z b.data.segments c.start c.dir).value u=
            (atomElemExpr c.terms z c.start c.dir).value u+(exprSum (b.data.segments.map
              (fun s => CellExpr.scale 2 (.segment s (-c.start,0) (-c.dir,0))))).value u := by
          unfold atomExpr atomElemExpr
          simp only [exprSum_value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
          ring
        rw [h0,exprSum_value,List.map_map]
        rfl
      rw [hv,evalModel_iadd]
      push_cast at h1 h2 ⊢
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
  have hbox := modelBox_spec S G hG _ _ _ _ hsum
  have hstart : (AtomOut.start ⟨c.backwards,0,0,0,0⟩ c.left c.right)=c.start := rfl
  have hparam_ok : ∀ u ∈ Set.Icc (0:ℝ) (w:ℝ),(c.start:ℝ)+(c.dir:ℝ)*u ∈ Set.Icc 1 4 := by
    intro u hu
    have hl : (1:ℝ) ≤ (c.left:ℝ) := by exact_mod_cast hg.1
    have hr4 : (c.right:ℝ) ≤ 4 := by exact_mod_cast hg.2.2
    have hwr : (w:ℝ)=(c.right:ℝ)-(c.left:ℝ) := by simp only [w]; push_cast; ring
    rw [hwr] at hu
    cases hb : c.backwards <;>
      simp only [AtomCellJ.start,AtomCellJ.dir,hb,Bool.false_eq_true,ite_false,ite_true,Rat.cast_neg,
        Rat.cast_one] <;> constructor <;> linarith [hu.1,hu.2]
  constructor
  · intro x hx
    change x ∈ Set.Icc ((c.left:ℚ):ℝ) ((c.right:ℚ):ℝ) at hx
    let u := if c.backwards then (c.right:ℝ)-x else x-(c.left:ℝ)
    have hu : u ∈ Set.Icc 0 (w:ℝ) := by
      simp only [w,Rat.cast_sub]
      cases hb : c.backwards <;> dsimp only [u] <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] <;>
        constructor <;> linarith [hx.1,hx.2]
    have hparam : (c.start:ℝ)+(c.dir:ℝ)*u=x := by
      cases hb : c.backwards <;> dsimp only [u] <;>
        simp only [AtomCellJ.start,AtomCellJ.dir,hb,Bool.false_eq_true,ite_false,ite_true,Rat.cast_neg,
          Rat.cast_one,one_mul,neg_one_mul] <;> ring
    have hv := hbox u hu
    rw [atomExpr_value _ _ hz b.data dw hd _ _ u (hparam_ok u hu)] at hv
    have hcoord : -(((c.start:ℝ):ℂ)+((c.dir:ℝ):ℂ)*(u:ℂ))= -(x:ℂ) := by
      have hh := congrArg (fun y : ℝ => -(y:ℂ)) hparam
      simpa only [Complex.ofReal_add,Complex.ofReal_mul] using hh
    rw [hparam,hcoord] at hv
    rw [W,atom_field_eq_extension]
    exact hv
  · intro u hu
    change u ∈ Set.Icc 0 (((c.right-c.left):ℚ):ℝ) at hu
    have hu' : u ∈ Set.Icc 0 (w:ℝ) := hu
    have hm := (abs_le.mp (hsum.2.2 u ⟨hu'.1,hu'.2⟩)).2
    have hl := upperLine_bound ((iadd c.field.coeff r.1).map (fun c : ℤ => (c:ℚ)/S)) w
      (c.field.remainder+(r.2:ℚ)/S) u hu'
    have e : qOf S (iadd c.field.coeff r.1)=((iadd c.field.coeff r.1).map (fun c : ℤ => (c:ℚ)/S)).map
        (fun x : ℚ => (x:ℝ)) := by simp [qOf,List.map_map]
    rw [e] at hm
    have h1 := le_roundUp G hG (upperLine ((iadd c.field.coeff r.1).map (fun c : ℤ => (c:ℚ)/S)) w
      (c.field.remainder+(r.2:ℚ)/S)).1
    have h2 := le_roundUp G hG (upperLine ((iadd c.field.coeff r.1).map (fun c : ℤ => (c:ℚ)/S)) w
      (c.field.remainder+(r.2:ℚ)/S)).2
    have h1r := Rat.cast_le (K := ℝ) |>.mpr h1
    have h2r := Rat.cast_le (K := ℝ) |>.mpr h2
    have hv := atomExpr_value c.terms z hz b.data dw hd c.start c.dir u (hparam_ok u hu')
    have hs : (((AtomOut.start ⟨c.backwards,0,0,0,0⟩ c.left c.right):ℚ):ℝ)=(c.start:ℝ) := rfl
    have hdir : (((AtomOut.dir ⟨c.backwards,0,0,0,0⟩):ℚ):ℝ)=(c.dir:ℝ) := rfl
    change omega (z:ℝ) ((c.start:ℝ)+(c.dir:ℝ)*u)-2*U b.data.dual.σ (-(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ)) ≤ _
    simp only [Complex.ofReal_add,Complex.ofReal_mul]
    rw [← hv]
    push_cast at hm hl ⊢
    nlinarith [mul_le_mul_of_nonneg_right h2r hu.1]

/-- All stored atom cells are sound: the per-cell hypotheses of the node assembly. -/
theorem nodeAtomPhysical_of_cells (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0)
    (b : BentInput) (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (cs : List (AtomCellJ × AtomOut)) (hcs : ∀ x ∈ cs,atomCellJ S G z b ss x.1=some x.2) :
    NodeAtomWPhysical z b cs ∧ NodeAtomLinePhysical z b cs :=
  ⟨fun x hx => (atomCellJ_sound S G hS hG z hz b dw hd ss hss x.1 x.2 (hcs x hx)).1,
   fun x hx => (atomCellJ_sound S G hS hG z hz b dw hd ss hss x.1 x.2 (hcs x hx)).2⟩


end CatalanCore.Li2.DecayCert.Seg
