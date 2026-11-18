module
public import CatalanCore.Li2.DecayCert.Seg.Ball
public import CatalanCore.Li2.DecayCert.Seg.NodeDefs
public import CatalanCore.Li2.DecayCert.Covers.Physical
public import CatalanCore.Li2.DecayCert.Covers.Geometry
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Own
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

theorem evalModel_smul (S k : ℤ) (u : ℝ) : ∀ a : List ℤ,
    evalModel (qOf S (a.map (fun c => k*c))) u=(k:ℝ)*evalModel (qOf S a) u
  | [] => by simp [qOf,evalModel_nil]
  | x::a => by
    simp only [qOf,List.map_cons] at *
    rw [evalModel_cons,evalModel_cons]
    have := evalModel_smul S k u a
    simp only [qOf] at this
    rw [this]; push_cast; ring

/-- Sums and integer multiples of integer models. -/
theorem modelsOn_iadd (S : ℤ) (f g : ℝ → ℝ) (a b : List ℤ) (lo hi ea eb : ℝ)
    (ha : ModelsOn f (qOf S a) lo hi ea) (hb : ModelsOn g (qOf S b) lo hi eb) :
    ModelsOn (fun u => f u+g u) (qOf S (iadd a b)) lo hi (ea+eb) := by
  refine ⟨ha.1,add_nonneg ha.2.1 hb.2.1,fun u hu => ?_⟩
  have h1 := ha.2.2 u hu; have h2 := hb.2.2 u hu
  rw [evalModel_iadd]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]

theorem modelsOn_smul (S k : ℤ) (f : ℝ → ℝ) (a : List ℤ) (lo hi e : ℝ)
    (ha : ModelsOn f (qOf S a) lo hi e) :
    ModelsOn (fun u => (k:ℝ)*f u) (qOf S (a.map (fun c => k*c))) lo hi (|(k:ℝ)| *e) := by
  refine ⟨ha.1,mul_nonneg (abs_nonneg _) ha.2.1,fun u hu => ?_⟩
  rw [evalModel_smul,← mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left (ha.2.2 u hu) (abs_nonneg _)

/-- The fused field model on `[lo,hi]` at scale `S`: compile, round, check. -/
noncomputable def fieldModelI (S : ℤ) (x : CellExpr) (lo hi : ℚ) (w : CellWitness) : Bool :=
  match LatticeGate.compileFast lo hi x w.model with
  | none => false
  | some m => decide (lo ≤ hi) && coefficientCheck S m w && remainderCheck S (max |lo| |hi|) m w

theorem fieldModelI_sound (S : ℤ) (x : CellExpr) (lo hi : ℚ) (w : CellWitness)
    (hp : PositiveSources x) (hc : fieldModelI S x lo hi w=true) :
    ModelsOn x.value (qOf S w.coeff) (lo:ℝ) hi w.remainder := by
  unfold fieldModelI at hc
  split at hc
  · contradiction
  rename_i m hm
  rw [LatticeGate.compileFast_eq] at hm
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0,hco⟩,hrm⟩ := hc
  have hR := of_decide_eq_true h0
  have h := roundModel_sound S lo hi m w x.value
    (compileModel_sound lo hi x w.model m hR hp hm) hco hrm
  have e : (gridCoeffs S w).map (fun q : ℚ => (q:ℝ))=qOf S w.coeff := by
    simp [gridCoeffs,qOf,List.map_map]
  rw [e] at h
  exact h

/-- One segment copy: a disc copy from the integer evaluator, or the segment's own polynomial
model (`.segOwn` witness) when the cell lies on the segment. -/
inductive SegCopy
  | disc (w : CopyI)
  | own (w : CellWitness)

noncomputable def copyOne (S : ℤ) (s : SegSharedI) (d : QSegment) (p e : CQ) (lo hi : ℚ) :
    SegCopy → Option (List ℤ×ℚ)
  | .disc w => match ballCopyJ S s d p e (max |lo| |hi|) w with
    | some o => some (o.1,(o.2:ℚ)/S)
    | none => none
  | .own w => if fieldModelI S (.segment d p e) lo hi w then some (w.coeff,w.remainder) else none

theorem abs_le_max_of_mem (lo hi : ℚ) (u : ℝ) (hu : u ∈ Set.Icc (lo:ℝ) hi) :
    |u| ≤ ((max |lo| |hi| : ℚ):ℝ) := by
  rw [Rat.cast_max,Rat.cast_abs,Rat.cast_abs]
  exact abs_le_max_abs_abs hu.1 hu.2

theorem copyOne_model (S : ℤ) (hS : 0 < S) (s : SegSharedI) (d : QSegment) (hsh : s.ok S d=true)
    (p e : CQ) (lo hi : ℚ) (hlh : lo ≤ hi) (w : SegCopy) (o : List ℤ×ℚ)
    (hpos : ∀ x ∈ Set.Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hc : copyOne S s d p e lo hi w=some o) :
    ModelsOn (CellExpr.segment d p e).value (qOf S o.1) (lo:ℝ) hi o.2 := by
  cases w with
  | disc w =>
    simp only [copyOne] at hc
    cases ho : ballCopyJ S s d p e (max |lo| |hi|) w with
    | none => simp [ho] at hc
    | some o' =>
    simp only [ho,Option.some.injEq] at hc
    subst hc
    have hm := ballCopyJ_model S hS s d hsh p e (max |lo| |hi|) w o' hpos ho
    have := hm.onIcc (lo:ℝ) hi (by exact_mod_cast hlh) (fun u hu => abs_le_max_of_mem lo hi u hu)
    simpa [qOf] using this
  | own w =>
    simp only [copyOne] at hc
    split_ifs at hc with hf
    simp only [Option.some.injEq] at hc
    subst hc
    exact fieldModelI_sound S _ lo hi w hpos hf

/-- The doubled copies of all segments, summed. -/
noncomputable def copySum (S : ℤ) (p e : CQ) (lo hi : ℚ) : List QSegment → List SegSharedI → List SegCopy →
    Option (List ℤ×ℚ)
  | [], [], [] => some ([],0)
  | d::ds, s::ss, w::ws => do
      let o ← copyOne S s d p e lo hi w
      let r ← copySum S p e lo hi ds ss ws
      pure (iadd (o.1.map (fun c => 2*c)) r.1,2*o.2+r.2)
  | _, _, _ => none

def sharedOK (S : ℤ) : List QSegment → List SegSharedI → Bool
  | [], [] => true
  | d::ds, s::ss => s.ok S d && sharedOK S ds ss
  | _, _ => false

theorem copySum_model (S : ℤ) (hS : 0 < S) (p e : CQ) (lo hi : ℚ) (hlh : lo ≤ hi) :
    ∀ (ds : List QSegment) (ss : List SegSharedI) (ws : List SegCopy) (r : List ℤ×ℚ),
    sharedOK S ds ss=true →
    (∀ d ∈ ds,∀ x ∈ Set.Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x) →
    copySum S p e lo hi ds ss ws=some r →
    ModelsOn (fun u => (ds.map (fun d => 2*(CellExpr.segment d p e).value u)).sum) (qOf S r.1)
      (lo:ℝ) hi r.2 := by
  have hRr : (lo:ℝ) ≤ hi := by exact_mod_cast hlh
  intro ds
  induction ds with
  | nil =>
    intro ss ws r _ _ h
    rcases ss with _|⟨s,ss⟩ <;> rcases ws with _|⟨w,ws⟩ <;> simp [copySum] at h
    subst h
    refine ⟨hRr,by simp,fun u _ => ?_⟩
    simp [qOf,evalModel_nil]
  | cons d ds ih =>
    intro ss ws r hok hpos h
    rcases ss with _|⟨s,ss⟩ <;> rcases ws with _|⟨w,ws⟩
    · simp [copySum] at h
    · simp [copySum] at h
    · simp [copySum] at h
    simp only [sharedOK,Bool.and_eq_true] at hok
    simp only [copySum] at h
    cases ho : copyOne S s d p e lo hi w with
    | none => simp [ho] at h
    | some o =>
    cases hr : copySum S p e lo hi ds ss ws with
    | none => simp [ho,hr] at h
    | some r' =>
    simp only [ho,hr,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.some.injEq] at h
    subst h
    have hm1 := copyOne_model S hS s d hok.1 p e lo hi hlh w o (hpos d List.mem_cons_self) ho
    have hm2 := ih ss ws r' hok.2 (fun d' hd' => hpos d' (List.mem_cons_of_mem _ hd')) hr
    refine ⟨hm1.1,?_,fun u hu => ?_⟩
    · have a1 := hm1.2.1; have a2 := hm2.2.1
      push_cast at a1 a2 ⊢; linarith
    · have h1 := hm1.2.2 u hu
      have h2 := hm2.2.2 u hu
      rw [evalModel_iadd,evalModel_two]
      simp only [List.map_cons,List.sum_cons]
      push_cast at h1 h2 ⊢
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]

/-! ### Outward rounding to a dyadic grid, bound boxes and dominating lines -/

def roundDn (G : ℤ) (x : ℚ) : ℚ := ((x.num*G/(x.den:ℤ):ℤ):ℚ)/G
def roundUp (G : ℤ) (x : ℚ) : ℚ := ((cdiv (x.num*G) (x.den:ℤ)):ℚ)/G

theorem roundDn_le (G : ℤ) (hG : 0 < G) (x : ℚ) : roundDn G x ≤ x := floor_scale_le x G hG
theorem le_roundUp (G : ℤ) (hG : 0 < G) (x : ℚ) : x ≤ roundUp G x := cdiv_scale_ge x G hG

/-- Bounds of an integer polynomial model on `[lo,hi]`, rounded outward to the grid `1/G`. -/
def modelBox (S G : ℤ) (cs : List ℤ) (err lo hi : ℚ) : QBox :=
  let a := cs.map (fun c : ℤ => (c:ℚ)/S)
  (roundDn G (polyLBQ a lo hi-err),roundUp G (polyUBQ a lo hi+err))

theorem modelBox_spec (S G : ℤ) (hG : 0 < G) (cs : List ℤ) (err lo hi : ℚ) (f : ℝ → ℝ)
    (hm : ModelsOn f (qOf S cs) (lo:ℝ) hi err) :
    ∀ u ∈ Set.Icc (lo:ℝ) (hi:ℝ),f u ∈ Set.Icc ((modelBox S G cs err lo hi).1:ℝ)
      ((modelBox S G cs err lo hi).2:ℝ) := by
  have e : qOf S cs=(cs.map (fun c : ℤ => (c:ℚ)/S)).map (fun x : ℚ => (x:ℝ)) := by
    simp [qOf,List.map_map]
  rw [e] at hm
  intro u hu
  have h := cell_ub_lb f _ lo hi err hm u hu
  have h1 : ((roundDn G (polyLBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) lo hi-err):ℚ):ℝ) ≤
      ((polyLBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) lo hi-err:ℚ):ℝ) := Rat.cast_le.mpr (roundDn_le G hG _)
  have h2 : ((polyUBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) lo hi+err:ℚ):ℝ) ≤
      ((roundUp G (polyUBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) lo hi+err):ℚ):ℝ) :=
    Rat.cast_le.mpr (le_roundUp G hG _)
  exact ⟨h1.trans h.1,h.2.trans h2⟩

/-- A line `A + B v` dominating a polynomial plus error on `[-R,R]`. -/
def symLine (co : List ℚ) (R err : ℚ) : ℚ×ℚ :=
  (coeffQ co 0+err+((List.range co.length).map (fun j : ℕ =>
      if 3 ≤ j then |coeffQ co j| *R^j else 0)).sum+(if 0 < coeffQ co 2 then coeffQ co 2*R^2 else 0),
    coeffQ co 1)

theorem symLine_bound (co : List ℚ) (R err : ℚ) (v : ℝ) (hv : v ∈ Set.Icc (-(R:ℝ)) R) :
    evalModel (co.map (fun q : ℚ => (q:ℝ))) v+(err:ℝ) ≤
      ((symLine co R err).1:ℝ)+((symLine co R err).2:ℝ)*v := by
  have hvabs : |v| ≤ (R:ℝ) := abs_le.mpr hv
  have htail : (∑ j ∈ Finset.range co.length,if 3 ≤ j then (coeffQ co j:ℝ)*v^j else 0) ≤
      ∑ j ∈ Finset.range co.length,if 3 ≤ j then |(coeffQ co j:ℝ)| *(R:ℝ)^j else 0 := by
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · calc
        _ ≤ |(coeffQ co j:ℝ)*v^j| := le_abs_self _
        _ = |(coeffQ co j:ℝ)| *|v|^j := by rw [abs_mul,abs_pow]
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg v) hvabs j) (abs_nonneg _)
    · exact le_rfl
  have hv2 : v^2 ≤ (R:ℝ)^2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg v) hvabs 2
  have hsq : (coeffQ co 2:ℝ)*v^2 ≤ (if (0:ℝ) < (coeffQ co 2:ℝ) then (coeffQ co 2:ℝ)*(R:ℝ)^2 else 0) := by
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left hv2 h.le
    · nlinarith [sq_nonneg v,not_lt.mp h]
  have hsum : (∑ j ∈ Finset.range co.length,((if 3 ≤ j then |coeffQ co j| *R^j else 0:ℚ):ℝ)) =
      ∑ j ∈ Finset.range co.length,if 3 ≤ j then |(coeffQ co j:ℝ)| *(R:ℝ)^j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> push_cast <;> rfl
  have hline : ((symLine co R err).1:ℝ)+((symLine co R err).2:ℝ)*v =
      (coeffQ co 0:ℝ)+(err:ℝ)+
      (∑ j ∈ Finset.range co.length,if 3 ≤ j then |(coeffQ co j:ℝ)| *(R:ℝ)^j else 0)+
      (if (0:ℝ) < (coeffQ co 2:ℝ) then (coeffQ co 2:ℝ)*(R:ℝ)^2 else 0)+(coeffQ co 1:ℝ)*v := by
    unfold symLine
    dsimp only
    rw [list_sum_map_range]
    by_cases hc : 0 < coeffQ co 2
    · have hcR : (0:ℝ) < (coeffQ co 2:ℝ) := by exact_mod_cast hc
      simp only [if_pos hc,if_pos hcR]
      push_cast
      rw [hsum]
    · have hcR : ¬(0:ℝ) < (coeffQ co 2:ℝ) := by exact_mod_cast hc
      simp only [if_neg hc,if_neg hcR]
      push_cast
      rw [hsum]
  rw [hline,evalModel_map_rat,sum_range_three_tail co.length (fun j => (coeffQ co j:ℝ)*v^j)
    (by intro j hj; rw [coeffQ_eq_zero_of_ge co j hj]; simp)]
  simp only [pow_zero,mul_one,pow_one]
  linarith

theorem positive_fieldExpr (terms : ℕ) (z : ℚ) (p e : CQ) : PositiveSources (fieldExpr terms z p e) := by
  simp [fieldExpr,exprSum,PositiveSources]

theorem point_param (o d : CQ) (m : ℚ) (v : ℝ) :
    cqReal (cqAdd o (cqScale m d))+cqReal d*(v:ℂ)=cqReal o+cqReal d*(((m:ℝ)+v:ℝ):ℂ) := by
  simp only [cqReal_add,cqReal_scale,Complex.ofReal_add,Complex.ofReal_ratCast]; ring

/-! ### Kernel-reducible twins of the old cell checkers

`compileModel` reaches the segment's own polynomial through a recursion the kernel does not
unfold; `LatticeGate.compileFast` is equal to it and reduces. Each twin below is proved equal to
the original checker, so every existing soundness lemma applies unchanged. -/

noncomputable def cellUBFast (x : CellInput) (w : CellWitness) : Bool :=
  match LatticeGate.compileFast x.lo x.hi x.expr w.model with
  | none => false
  | some m => decide (x.lo ≤ x.hi) && coefficientCheck x.scale m w &&
      remainderCheck x.scale (max |x.lo| |x.hi|) m w &&
      decide (polyUBQ (gridCoeffs x.scale w) x.lo x.hi+w.remainder ≤ w.ub ∧
        w.lb ≤ polyLBQ (gridCoeffs x.scale w) x.lo x.hi-w.remainder)

theorem cellUBFast_eq (x : CellInput) (w : CellWitness) : cellUBFast x w=cellUBF x w := by
  unfold cellUBFast cellUBF; rw [LatticeGate.compileFast_eq]
  cases compileModel x.lo x.hi x.expr w.model <;> rfl

noncomputable def lineCellFast (x : CellInput) (w : LineWitness) : Bool :=
  cellUBFast x w.cell && decide (x.lo=0 ∧ 0 ≤ x.hi) &&
    let line := upperLine (gridCoeffs x.scale w.cell) x.hi w.cell.remainder
    decide (line.1 ≤ w.a ∧ line.1+line.2*x.hi ≤ w.a+w.b*x.hi)

theorem lineCellFast_eq (x : CellInput) (w : LineWitness) : lineCellFast x w=lineCellF x w := by
  unfold lineCellFast lineCellF; rw [cellUBFast_eq]

noncomputable def holderCellBoundsFast (z : ℚ) (d : SegmentDatum) (c : NodeCell)
    (w : HolderCellWitness) : Option QBox := do
  if ¬(0 < c.width ∧ w.points.length=d.segments.length ∧ w.copies.length=d.segments.length)
    then none else
    if cellUBFast (makeCell c (fieldExpr c.terms z c.p c.e)) w.field=false then none else
      let bounds ← (List.range d.segments.length).mapM (fun j => do
        let s ← d.segments[j]?
        let p ← w.points[j]?
        let h ← w.copies[j]?
        if cellUBFast (endpointCell c (.segment s c.p c.e)) p=false then none else
          let H ← holderCopyBound s c.p c.e c.width h
          pure (p.lb-H,p.ub+H))
      pure (w.field.lb+2*(bounds.map Prod.fst).sum,
        w.field.ub+2*(bounds.map Prod.snd).sum)

noncomputable def fieldCellBoundsFast (z : ℚ) (d : SegmentDatum) (c : NodeCell) :
    FieldMethod → Option QBox
  | .taylor w =>
      if cellUBFast (makeCell c (WExpr c.terms z d.segments c.p c.e)) w then some (w.lb,w.ub) else none
  | .holder w => holderCellBoundsFast z d c w

theorem fieldCellBoundsFast_eq (z : ℚ) (d : SegmentDatum) (c : NodeCell) (f : FieldMethod) :
    fieldCellBoundsFast z d c f=fieldCellBounds z d c f := by
  cases f <;> simp only [fieldCellBoundsFast,fieldCellBounds,holderCellBoundsFast,holderCellBounds,
    cellUBFast_eq]

noncomputable def contourBoundsFast (z : ℚ) (b : BentInput) (c : ContourCell) : Option QBox :=
  if c.edge ≤ b.geom.polygon.edges ∧ 0 ≤ c.left ∧ c.left < c.right ∧
      c.right ≤ edgeLimit b c.edge then
    fieldCellBoundsFast z b.data (contourNodeCell b c) c.method else none

theorem contourBoundsFast_eq (z : ℚ) (b : BentInput) (c : ContourCell) :
    contourBoundsFast z b c=contourBounds z b c := by
  unfold contourBoundsFast contourBounds; rw [fieldCellBoundsFast_eq]

noncomputable def atomCellCheckFast (z : ℚ) (d : SegmentDatum) (c : AtomCell) : Bool :=
  decide (1 ≤ c.left ∧ c.left < c.right ∧ c.right ≤ 4) &&
    lineCellFast (atomCellInput z d c) c.witness

theorem atomCellCheckFast_eq (z : ℚ) (d : SegmentDatum) (c : AtomCell) :
    atomCellCheckFast z d c=atomCellCheck z d c := by
  unfold atomCellCheckFast atomCellCheck; rw [lineCellFast_eq]

/-! ### Contour cells -/

/-- A contour cell on `[left,right]` of an edge, expanded at its midpoint: the field model witness
and one copy per segment. -/
structure ContourCellJ where
  edge : ℕ
  left : ℚ
  right : ℚ
  terms : ℕ
  field : CellWitness
  copies : List SegCopy

def ContourCellJ.mid (c : ContourCellJ) : ℚ := (c.left+c.right)/2
def ContourCellJ.rad (c : ContourCellJ) : ℚ := (c.right-c.left)/2

noncomputable def contourCellJ (S G : ℤ) (z : ℚ) (b : BentInput) (ss : List SegSharedI) (c : ContourCellJ) :
    Option QBox :=
  if c.edge ≤ b.geom.polygon.edges ∧ 0 ≤ c.left ∧ c.left < c.right ∧ c.right ≤ edgeLimit b c.edge then
    if fieldModelI S (fieldExpr c.terms z (cqAdd (edgeOrigin b c.edge) (cqScale c.mid (edgeDirection b c.edge)))
        (edgeDirection b c.edge)) (-c.rad) c.rad c.field then
      match copySum S (cqAdd (edgeOrigin b c.edge) (cqScale c.mid (edgeDirection b c.edge)))
          (edgeDirection b c.edge) (-c.rad) c.rad b.data.segments ss c.copies with
      | some r => some (modelBox S G (iadd c.field.coeff r.1) (c.field.remainder+r.2) (-c.rad) c.rad)
      | none => none
    else none
  else none

theorem contourCellJ_sound (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (c : ContourCellJ) (B : QBox) (hc : contourCellJ S G z b ss c=some B) :
    ∀ t ∈ Set.Icc ((c.left:ℚ):ℝ) ((c.right:ℚ):ℝ),
      W (z:ℝ) b.data.dual.σ (cqReal (edgeOrigin b c.edge)+
        cqReal (edgeDirection b c.edge)*(t:ℂ)) ∈ Set.Icc (B.1:ℝ) (B.2:ℝ) := by
  unfold contourCellJ at hc
  split_ifs at hc with hg hf
  set p := cqAdd (edgeOrigin b c.edge) (cqScale c.mid (edgeDirection b c.edge)) with hp
  set e := edgeDirection b c.edge with he
  cases hr : copySum S p e (-c.rad) c.rad b.data.segments ss c.copies with
  | none => simp [hr] at hc
  | some r =>
  simp only [hr,Option.some.injEq] at hc
  subst hc
  have hR0 : (0:ℚ) ≤ c.rad := by simp only [ContourCellJ.rad]; linarith [hg.2.2.1]
  have hF := fieldModelI_sound S _ _ _ _ (positive_fieldExpr _ _ _ _) hf
  have hpos := (datumCheck_positive b.data dw hd).1
  have hC := copySum_model S hS p e (-c.rad) c.rad (by linarith) _ ss c.copies r hss hpos hr
  rw [Rat.cast_neg] at hF hC
  have hsum : ModelsOn (WExpr c.terms z b.data.segments p e).value
      (qOf S (iadd c.field.coeff r.1)) (-(c.rad:ℝ)) c.rad (((c.field.remainder+r.2):ℚ):ℝ) := by
    refine ⟨hF.1,?_,fun u hu => ?_⟩
    · have := hF.2.1; have := hC.2.1; push_cast at *; linarith
    · have h1 := hF.2.2 u hu
      have h2 := hC.2.2 u hu
      have hv : (WExpr c.terms z b.data.segments p e).value u=
          (fieldExpr c.terms z p e).value u+
            (b.data.segments.map (fun d => 2*(CellExpr.segment d p e).value u)).sum := by
        change (fieldExpr c.terms z p e).value u+
          (exprSum (b.data.segments.map (fun s => .scale 2 (.segment s p e)))).value u=_
        rw [exprSum_value,List.map_map]
        rfl
      rw [hv,evalModel_iadd]
      push_cast at h1 h2 ⊢
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
  have hbox := modelBox_spec S G hG (iadd c.field.coeff r.1) (c.field.remainder+r.2) (-c.rad) c.rad _ (by rw [Rat.cast_neg]; exact hsum)
  rw [Rat.cast_neg] at hbox
  intro t ht
  have hmid : ((c.mid:ℚ):ℝ)=(((c.left:ℚ):ℝ)+((c.right:ℚ):ℝ))/2 := by
    simp only [ContourCellJ.mid]; push_cast; ring
  have hrad : ((c.rad:ℚ):ℝ)=(((c.right:ℚ):ℝ)-((c.left:ℚ):ℝ))/2 := by
    simp only [ContourCellJ.rad]; push_cast; ring
  have hu : t-((c.mid:ℚ):ℝ) ∈ Set.Icc (-((c.rad:ℚ):ℝ)) ((c.rad:ℚ):ℝ) := by
    rw [hmid,hrad]; constructor <;> linarith [ht.1,ht.2]
  have hpt : cqReal p+cqReal e*((t-((c.mid:ℚ):ℝ):ℝ):ℂ)=cqReal (edgeOrigin b c.edge)+cqReal e*(t:ℂ) := by
    rw [hp,point_param]; congr 2; push_cast; ring
  have hl0 : (0:ℝ) ≤ ((c.left:ℚ):ℝ) := by exact_mod_cast hg.2.1
  have hrE : ((c.right:ℚ):ℝ) ≤ ((edgeLimit b c.edge:ℚ):ℝ) := by exact_mod_cast hg.2.2.2
  have hquad := bent_edge_quadrant b c.edge hg.1 t ⟨by linarith [ht.1],by linarith [ht.2]⟩
  rw [← he, ← hpt] at hquad
  have hv := hbox _ hu
  rw [WExpr_value _ _ hz b.data dw hd _ _ _ hquad.1 hquad.2,hpt] at hv
  exact hv

/-- A contour cell: a Taylor cell from integer copies, or an existing branch-point (Hölder) cell. -/
inductive ContourCellN
  | taylor (c : ContourCellJ)
  | holder (c : ContourCell)

def ContourCellN.edge : ContourCellN → ℕ
  | .taylor c => c.edge
  | .holder c => c.edge
def ContourCellN.left : ContourCellN → ℚ
  | .taylor c => c.left
  | .holder c => c.left
def ContourCellN.right : ContourCellN → ℚ
  | .taylor c => c.right
  | .holder c => c.right

instance : ContourProj ContourCellN := ⟨ContourCellN.edge,ContourCellN.left,ContourCellN.right⟩

noncomputable def contourCellN (S G : ℤ) (z : ℚ) (b : BentInput) (ss : List SegSharedI) :
    ContourCellN → Option QBox
  | .taylor c => contourCellJ S G z b ss c
  | .holder c => contourBoundsFast z b c

theorem contourCellN_sound (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (c : ContourCellN) (B : QBox) (hc : contourCellN S G z b ss c=some B) :
    ∀ t ∈ Set.Icc ((ContourProj.left c:ℚ):ℝ) ((ContourProj.right c:ℚ):ℝ),
      W (z:ℝ) b.data.dual.σ (cqReal (edgeOrigin b (ContourProj.edge c))+
        cqReal (edgeDirection b (ContourProj.edge c))*(t:ℂ)) ∈ Set.Icc (B.1:ℝ) (B.2:ℝ) := by
  cases c with
  | taylor c => exact contourCellJ_sound S G hS hG z hz b dw hd ss hss c B hc
  | holder c =>
    rw [contourCellN,contourBoundsFast_eq] at hc
    exact contourBounds_physical z hz b dw hd c B hc

/-- Stored contour box check: the computed box lies inside the stored one. -/
noncomputable def contourCellOK (S G : ℤ) (z : ℚ) (b : BentInput) (ss : List SegSharedI)
    (c : ContourCellN) (B : QBox) : Bool :=
  match contourCellN S G z b ss c with
  | some B' => decide (B.1 ≤ B'.1 ∧ B'.2 ≤ B.2)
  | none => false

theorem contourCellOK_sound (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (c : ContourCellN) (B : QBox) (hc : contourCellOK S G z b ss c B=true) :
    ∀ t ∈ Set.Icc ((ContourProj.left c:ℚ):ℝ) ((ContourProj.right c:ℚ):ℝ),
      W (z:ℝ) b.data.dual.σ (cqReal (edgeOrigin b (ContourProj.edge c))+
        cqReal (edgeDirection b (ContourProj.edge c))*(t:ℂ)) ∈ Set.Icc (B.1:ℝ) (B.2:ℝ) := by
  unfold contourCellOK at hc
  cases h : contourCellN S G z b ss c with
  | none => simp [h] at hc
  | some B' =>
  simp only [h,decide_eq_true_eq] at hc
  intro t ht
  have hw := contourCellN_sound S G hS hG z hz b dw hd ss hss c B' h t ht
  have h1 : (B.1:ℝ) ≤ B'.1 := by exact_mod_cast hc.1
  have h2 : (B'.2:ℝ) ≤ B.2 := by exact_mod_cast hc.2
  exact ⟨h1.trans hw.1,hw.2.trans h2⟩

/-- All stored contour cells are sound: the per-cell hypothesis of the node assembly. -/
theorem nodeContourPhysical_of_cells (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0)
    (b : BentInput) (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (cs : List (ContourCellN × QBox)) (hcs : ∀ x ∈ cs,contourCellOK S G z b ss x.1 x.2=true) :
    NodeContourPhysical z b cs :=
  fun x hx => contourCellOK_sound S G hS hG z hz b dw hd ss hss x.1 x.2 (hcs x hx)

/-! ### Atom cells -/

/-- An atom cell on `[left,right] ⊂ [1,4]`, expanded at its midpoint. -/
structure AtomCellJ where
  left : ℚ
  right : ℚ
  terms : ℕ
  field : CellWitness
  copies : List SegCopy

instance : AtomProj AtomCellJ := ⟨AtomCellJ.left,AtomCellJ.right⟩

def AtomCellJ.mid (c : AtomCellJ) : ℚ := (c.left+c.right)/2
def AtomCellJ.rad (c : AtomCellJ) : ℚ := (c.right-c.left)/2

/-- The elementary (non-segment) part of `atomExpr`. -/
def atomElemExpr (terms : ℕ) (z x dir : ℚ) : CellExpr :=
  exprSum [.scale 2 (.xlog x dir), .scale (-3) (.xlog (x-1) dir),
    .scale (-1) (.xlog (4-x) (-dir)),
    .linear (seAdd (.rat 1) (seScale (-x) (.log terms |z|)))
      (seScale (-dir) (.log terms |z|))]

noncomputable def atomCellJ (S G : ℤ) (z : ℚ) (b : BentInput) (ss : List SegSharedI) (c : AtomCellJ) :
    Option AtomOut :=
  if 1 ≤ c.left ∧ c.left < c.right ∧ c.right ≤ 4 then
    if fieldModelI S (atomElemExpr c.terms z c.mid 1) (-c.rad) c.rad c.field then
      match copySum S (-c.mid,0) (-1,0) (-c.rad) c.rad b.data.segments ss c.copies with
      | some r =>
        let cs := iadd c.field.coeff r.1
        let err := c.field.remainder+r.2
        let bx := modelBox S G cs err (-c.rad) c.rad
        let line := symLine (cs.map (fun c : ℤ => (c:ℚ)/S)) c.rad err
        some ⟨false,roundUp G (line.1-line.2*c.rad),roundUp G line.2,bx.1,bx.2⟩
      | none => none
    else none
  else none

theorem atomCellJ_sound (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (c : AtomCellJ) (o : AtomOut) (hc : atomCellJ S G z b ss c=some o) :
    (∀ t ∈ Set.Icc ((c.left:ℚ):ℝ) ((c.right:ℚ):ℝ),
      W (z:ℝ) b.data.dual.σ (-(t:ℂ)) ∈ Set.Icc (o.lb:ℝ) (o.ub:ℝ)) ∧
    (∀ u ∈ Set.Icc (0:ℝ) ((c.right-c.left:ℚ):ℝ),
      omega (z:ℝ) (((o.start c.left c.right:ℚ):ℝ)+((o.dir:ℚ):ℝ)*u)-
        2*U b.data.dual.σ (-((((o.start c.left c.right:ℚ):ℝ)+
          ((o.dir:ℚ):ℝ)*u:ℝ):ℂ)) ≤ (o.a:ℝ)+(o.b:ℝ)*u) := by
  unfold atomCellJ at hc
  split_ifs at hc with hg hf
  cases hr : copySum S (-c.mid,0) (-1,0) (-c.rad) c.rad b.data.segments ss c.copies with
  | none => simp [hr] at hc
  | some r =>
  simp only [hr,Option.some.injEq] at hc
  subst hc
  have hR0 : (0:ℚ) ≤ c.rad := by simp only [AtomCellJ.rad]; linarith [hg.2.1]
  have hF := fieldModelI_sound S _ _ _ _ (by
    simp [atomElemExpr,exprSum,PositiveSources]) hf
  have hpos := (datumCheck_positive b.data dw hd).1
  have hC := copySum_model S hS _ _ (-c.rad) c.rad (by linarith) _ ss c.copies r hss hpos hr
  rw [Rat.cast_neg] at hF hC
  have hsum : ModelsOn (atomExpr c.terms z b.data.segments c.mid 1).value
      (qOf S (iadd c.field.coeff r.1)) (-(c.rad:ℝ)) c.rad (((c.field.remainder+r.2):ℚ):ℝ) := by
    refine ⟨hF.1,?_,fun u hu => ?_⟩
    · have := hF.2.1; have := hC.2.1; push_cast at *; linarith
    · have h1 := hF.2.2 u hu
      have h2 := hC.2.2 u hu
      have hv : (atomExpr c.terms z b.data.segments c.mid 1).value u=
          (atomElemExpr c.terms z c.mid 1).value u+
            (b.data.segments.map (fun d => 2*(CellExpr.segment d (-c.mid,0) (-1,0)).value u)).sum := by
        have h0 : (atomExpr c.terms z b.data.segments c.mid 1).value u=
            (atomElemExpr c.terms z c.mid 1).value u+(exprSum (b.data.segments.map
              (fun s => CellExpr.scale 2 (.segment s (-c.mid,0) (-1,0))))).value u := by
          unfold atomExpr atomElemExpr
          simp only [exprSum_value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
            List.map_append,List.sum_append]
          ring
        rw [h0,exprSum_value,List.map_map]
        rfl
      rw [hv,evalModel_iadd]
      push_cast at h1 h2 ⊢
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
  have hbox := modelBox_spec S G hG (iadd c.field.coeff r.1) (c.field.remainder+r.2) (-c.rad) c.rad _ (by rw [Rat.cast_neg]; exact hsum)
  rw [Rat.cast_neg] at hbox
  have hmid : ((c.mid:ℚ):ℝ)=(((c.left:ℚ):ℝ)+((c.right:ℚ):ℝ))/2 := by
    simp only [AtomCellJ.mid]; push_cast; ring
  have hrad : ((c.rad:ℚ):ℝ)=(((c.right:ℚ):ℝ)-((c.left:ℚ):ℝ))/2 := by
    simp only [AtomCellJ.rad]; push_cast; ring
  have hl1 : (1:ℝ) ≤ ((c.left:ℚ):ℝ) := by exact_mod_cast hg.1
  have hr4 : ((c.right:ℚ):ℝ) ≤ 4 := by exact_mod_cast hg.2.2
  have hin : ∀ v ∈ Set.Icc (-((c.rad:ℚ):ℝ)) ((c.rad:ℚ):ℝ),
      ((c.mid:ℚ):ℝ)+((1:ℚ):ℝ)*v ∈ Set.Icc (1:ℝ) 4 := by
    intro v hv
    have h1 := hv.1; have h2 := hv.2
    rw [hrad] at h1 h2
    rw [hmid,Rat.cast_one,one_mul]
    constructor <;> linarith
  constructor
  · intro x hx
    have hu : x-((c.mid:ℚ):ℝ) ∈ Set.Icc (-((c.rad:ℚ):ℝ)) ((c.rad:ℚ):ℝ) := by
      rw [hmid,hrad]; constructor <;> linarith [hx.1,hx.2]
    have hv := hbox _ hu
    rw [atomExpr_value _ _ hz b.data dw hd _ _ _ (hin _ hu)] at hv
    have hx' : ((c.mid:ℚ):ℝ)+((1:ℚ):ℝ)*(x-((c.mid:ℚ):ℝ))=x := by rw [Rat.cast_one]; ring
    have hcoord : -((((c.mid:ℚ):ℝ):ℂ)+(((1:ℚ):ℝ):ℂ)*(((x-((c.mid:ℚ):ℝ)):ℝ):ℂ))= -(x:ℂ) := by
      have hh := congrArg (fun y : ℝ => -(y:ℂ)) hx'
      simpa only [Complex.ofReal_add,Complex.ofReal_mul] using hh
    rw [hx',hcoord] at hv
    rw [W,atom_field_eq_extension]
    exact hv
  · intro u hu
    have hu2 : u ≤ ((c.right:ℚ):ℝ)-((c.left:ℚ):ℝ) := by have := hu.2; push_cast at this; exact this
    have hvI : u-((c.rad:ℚ):ℝ) ∈ Set.Icc (-((c.rad:ℚ):ℝ)) ((c.rad:ℚ):ℝ) := by
      rw [hrad]; constructor <;> linarith [hu.1]
    have hm := (abs_le.mp (hsum.2.2 _ hvI)).2
    have e : qOf S (iadd c.field.coeff r.1)=((iadd c.field.coeff r.1).map (fun c : ℤ => (c:ℚ)/S)).map
        (fun x : ℚ => (x:ℝ)) := by simp [qOf,List.map_map]
    rw [e] at hm
    have hl := symLine_bound ((iadd c.field.coeff r.1).map (fun c : ℤ => (c:ℚ)/S)) c.rad
      (c.field.remainder+r.2) _ hvI
    have h1 := Rat.cast_le (K := ℝ) |>.mpr (le_roundUp G hG
      ((symLine ((iadd c.field.coeff r.1).map (fun c : ℤ => (c:ℚ)/S)) c.rad (c.field.remainder+r.2)).1-
       (symLine ((iadd c.field.coeff r.1).map (fun c : ℤ => (c:ℚ)/S)) c.rad (c.field.remainder+r.2)).2*c.rad))
    have h2 := Rat.cast_le (K := ℝ) |>.mpr (le_roundUp G hG
      (symLine ((iadd c.field.coeff r.1).map (fun c : ℤ => (c:ℚ)/S)) c.rad (c.field.remainder+r.2)).2)
    have hval := atomExpr_value c.terms z hz b.data dw hd c.mid 1 _ (hin _ hvI)
    have hpt : ((c.mid:ℚ):ℝ)+((1:ℚ):ℝ)*(u-((c.rad:ℚ):ℝ))=((c.left:ℚ):ℝ)+u := by
      rw [hmid,hrad,Rat.cast_one]; ring
    have hcoord : -((((c.mid:ℚ):ℝ):ℂ)+(((1:ℚ):ℝ):ℂ)*(((u-((c.rad:ℚ):ℝ)):ℝ):ℂ))=
        -(((((c.left:ℚ):ℝ)+u):ℝ):ℂ) := by
      have hh := congrArg (fun y : ℝ => -(y:ℂ)) hpt
      simpa only [Complex.ofReal_add,Complex.ofReal_mul] using hh
    rw [hpt,hcoord] at hval
    simp only [AtomOut.start,AtomOut.dir,Bool.false_eq_true,↓reduceIte,Rat.cast_one,one_mul]
    rw [← hval]
    have hu0 := hu.1
    set L := symLine ((iadd c.field.coeff r.1).map (fun c : ℤ => (c:ℚ)/S)) c.rad (c.field.remainder+r.2)
    have hB := mul_le_mul_of_nonneg_right h2 hu0
    push_cast at hm hl h1 h2 hB ⊢
    nlinarith [hm,hl,h1,hB]

/-- A stored atom output with the same orientation, wider `W` bounds and a line above the computed
line at both ends of the cell is sound whenever the computed output is. -/
theorem atomOut_relax (f g : ℝ → ℝ) (l r : ℚ) (o o' : AtomOut) (hbw : o.backwards=o'.backwards)
    (hlr : l < r) (hlb : o.lb ≤ o'.lb) (hub : o'.ub ≤ o.ub) (ha : o'.a ≤ o.a)
    (hab : o'.a+o'.b*(r-l) ≤ o.a+o.b*(r-l))
    (hs : (∀ t ∈ Set.Icc (l:ℝ) (r:ℝ),f t ∈ Set.Icc (o'.lb:ℝ) (o'.ub:ℝ)) ∧
      (∀ u ∈ Set.Icc (0:ℝ) ((r-l:ℚ):ℝ),g (((o'.start l r:ℚ):ℝ)+((o'.dir:ℚ):ℝ)*u) ≤ (o'.a:ℝ)+(o'.b:ℝ)*u)) :
    (∀ t ∈ Set.Icc (l:ℝ) (r:ℝ),f t ∈ Set.Icc (o.lb:ℝ) (o.ub:ℝ)) ∧
      (∀ u ∈ Set.Icc (0:ℝ) ((r-l:ℚ):ℝ),g (((o.start l r:ℚ):ℝ)+((o.dir:ℚ):ℝ)*u) ≤ (o.a:ℝ)+(o.b:ℝ)*u) := by
  refine ⟨fun t ht => ?_,fun u hu => ?_⟩
  · have hw := hs.1 t ht
    have h1 : (o.lb:ℝ) ≤ o'.lb := by exact_mod_cast hlb
    have h2 : (o'.ub:ℝ) ≤ o.ub := by exact_mod_cast hub
    exact ⟨h1.trans hw.1,hw.2.trans h2⟩
  · have hw := hs.2 u hu
    have hst : o.start l r=o'.start l r := by simp [AtomOut.start,hbw]
    have hdir : o.dir=o'.dir := by simp [AtomOut.dir,hbw]
    rw [hst,hdir]
    refine hw.trans ?_
    have hwpos : (0:ℝ) < ((r-l:ℚ):ℝ) := by
      have : (0:ℚ) < r-l := by linarith
      exact_mod_cast this
    have ha' : (o'.a:ℝ) ≤ o.a := by exact_mod_cast ha
    have hab' : (o'.a:ℝ)+(o'.b:ℝ)*((r-l:ℚ):ℝ) ≤ (o.a:ℝ)+(o.b:ℝ)*((r-l:ℚ):ℝ) := by
      exact_mod_cast hab
    set w : ℝ := ((r-l:ℚ):ℝ)
    have hu0 := hu.1; have hu1 := hu.2
    have key : ((o.a:ℝ)+(o.b:ℝ)*u-((o'.a:ℝ)+(o'.b:ℝ)*u))*w=
        (w-u)*((o.a:ℝ)-(o'.a:ℝ))+u*(((o.a:ℝ)+(o.b:ℝ)*w)-((o'.a:ℝ)+(o'.b:ℝ)*w)) := by ring
    have hnn : 0 ≤ ((o.a:ℝ)+(o.b:ℝ)*u-((o'.a:ℝ)+(o'.b:ℝ)*u))*w := by
      rw [key]; exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hu0 (by linarith))
    have := nonneg_of_mul_nonneg_left hnn hwpos
    linarith

/-- Stored atom output check: forward orientation, computed `W` bounds inside the stored ones, and
the stored line above the computed line at both ends of the cell. -/
noncomputable def atomCellOK (S G : ℤ) (z : ℚ) (b : BentInput) (ss : List SegSharedI) (c : AtomCellJ)
    (o : AtomOut) : Bool :=
  match atomCellJ S G z b ss c with
  | some o' => decide (o.backwards=false ∧ c.left < c.right ∧ o.lb ≤ o'.lb ∧ o'.ub ≤ o.ub ∧ o'.a ≤ o.a ∧
      o'.a+o'.b*(c.right-c.left) ≤ o.a+o.b*(c.right-c.left))
  | none => false

theorem atomCellOK_sound (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (c : AtomCellJ) (o : AtomOut) (hc : atomCellOK S G z b ss c o=true) :
    (∀ t ∈ Set.Icc ((c.left:ℚ):ℝ) ((c.right:ℚ):ℝ),
      W (z:ℝ) b.data.dual.σ (-(t:ℂ)) ∈ Set.Icc (o.lb:ℝ) (o.ub:ℝ)) ∧
    (∀ u ∈ Set.Icc (0:ℝ) ((c.right-c.left:ℚ):ℝ),
      omega (z:ℝ) (((o.start c.left c.right:ℚ):ℝ)+((o.dir:ℚ):ℝ)*u)-
        2*U b.data.dual.σ (-((((o.start c.left c.right:ℚ):ℝ)+
          ((o.dir:ℚ):ℝ)*u:ℝ):ℂ)) ≤ (o.a:ℝ)+(o.b:ℝ)*u) := by
  unfold atomCellOK at hc
  cases h : atomCellJ S G z b ss c with
  | none => simp [h] at hc
  | some o' =>
  simp only [h,decide_eq_true_eq] at hc
  obtain ⟨hb,hlr,hlb,hub,ha,hab⟩ := hc
  have hb' : o'.backwards=false := by
    unfold atomCellJ at h
    split_ifs at h
    split at h
    · simp only [Option.some.injEq] at h; rw [← h]
    · simp at h
  exact atomOut_relax (fun t => W (z:ℝ) b.data.dual.σ (-(t:ℂ)))
    (fun x => omega (z:ℝ) x-2*U b.data.dual.σ (-(x:ℂ))) c.left c.right o o' (by rw [hb,hb'])
    hlr hlb hub ha hab (atomCellJ_sound S G hS hG z hz b dw hd ss hss c o' h)

/-! ### The singular term at an anchored end

At `x=1` (forward) or `x=4` (backwards) one logarithmic term of the atom field is a multiple of
`u log u`. On `[0,w]` it is modelled by its tangent at `w/2`, raised by half the gap `w/2`. -/

theorem xlog_tangent_gap (u0 u : ℝ) (h0 : 0 < u0) (hu : 0 ≤ u) (hu2 : u ≤ 2*u0) :
    0 ≤ xlog u-((Real.log u0+1)*u-u0) ∧ xlog u-((Real.log u0+1)*u-u0) ≤ u0 := by
  unfold xlog
  rcases hu.eq_or_lt with h | h
  · subst h; simp only [Real.log_zero,mul_zero,zero_mul,zero_sub,sub_neg_eq_add,zero_add]
    exact ⟨h0.le,le_rfl⟩
  have hx : 0 < u/u0 := div_pos h h0
  have hlog : Real.log u=Real.log (u/u0)+Real.log u0 := by
    rw [Real.log_div h.ne' h0.ne']; ring
  have hl1 := Real.log_le_sub_one_of_pos hx
  have hl2 := Real.one_sub_inv_le_log_of_pos hx
  rw [inv_div] at hl2
  have hdiv1 : u/u0 ≤ 2 := by rw [div_le_iff₀ h0]; linarith
  have e1 : u*(u0/u)=u0 := by field_simp
  rw [hlog]
  set L := Real.log (u/u0)
  constructor
  · have := mul_le_mul_of_nonneg_left hl2 h.le
    rw [mul_sub,mul_one,e1] at this
    nlinarith
  · have hL1 : L ≤ 1 := by linarith
    have := mul_le_mul_of_nonneg_left hL1 h.le
    nlinarith

/-- The tangent model of `u log u` on `[0,w]`. -/
def xlogTangent (terms : ℕ) (w : ℚ) : CompiledModel :=
  ⟨[seRat (-(w/4)),seAdd (.log terms (w/2)) (seRat 1)],seRat (w/4)⟩

theorem xlogTangent_models (terms : ℕ) (w : ℚ) (hw : 0 < w) :
    ModelsOn (fun u => xlog u) ((xlogTangent terms w).coeff.map ScalarExpr.value) (0:ℚ) w
      (xlogTangent terms w).error.value := by
  have hw' : (0:ℝ) < w := by exact_mod_cast hw
  refine ⟨by exact_mod_cast hw.le,?_,fun u hu => ?_⟩
  · simp only [xlogTangent,seRat_value]; push_cast; linarith
  · simp only [xlogTangent,List.map_cons,List.map_nil,seRat_value,seAdd_value]
    rw [evalModel_cons,evalModel_cons,evalModel_nil]
    have hu1 : (0:ℝ) ≤ u := by have := hu.1; push_cast at this; exact this
    have hu2 : u ≤ (w:ℝ) := hu.2
    have h0 : (0:ℝ) < ((w/2:ℚ):ℝ) := by push_cast; linarith
    have g := xlog_tangent_gap ((w/2:ℚ):ℝ) u h0 hu1 (by push_cast; linarith)
    change |xlog u-(((-(w/4):ℚ):ℝ)+u*(Real.log ((w/2:ℚ):ℝ)+((1:ℚ):ℝ)+u*0))| ≤ ((w/4:ℚ):ℝ)
    rw [abs_le]
    push_cast at g ⊢
    constructor <;> nlinarith [g.1,g.2]

/-- The integer tangent model at scale `S`, checked against the exact one. -/
noncomputable def tangentI (S : ℤ) (terms : ℕ) (w : ℚ) (sw : CellWitness) : Bool :=
  decide (0 < w) && coefficientCheck S (xlogTangent terms w) sw &&
    remainderCheck S (max |(0:ℚ)| |w|) (xlogTangent terms w) sw

theorem tangentI_sound (S : ℤ) (terms : ℕ) (w : ℚ) (sw : CellWitness) (h : tangentI S terms w sw=true) :
    ModelsOn (fun u => xlog u) (qOf S sw.coeff) (0:ℚ) w sw.remainder := by
  simp only [tangentI,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨hw,hco⟩,hrm⟩ := h
  have hm := roundModel_sound S 0 w (xlogTangent terms w) sw _ (xlogTangent_models terms w hw) hco hrm
  have e : (gridCoeffs S sw).map (fun q : ℚ => (q:ℝ))=qOf S sw.coeff := by
    simp [gridCoeffs,qOf,List.map_map]
  rw [e] at hm
  exact hm

/-- The atom field at an anchored end without its singular term, and that term's multiple. -/
def atomRegExpr (terms : ℕ) (z x dir : ℚ) (b : Bool) : CellExpr :=
  let lin := CellExpr.linear (seAdd (.rat 1) (seScale (-x) (.log terms |z|)))
    (seScale (-dir) (.log terms |z|))
  if b then exprSum [.scale 2 (.xlog x dir),.scale (-3) (.xlog (x-1) dir),lin]
  else exprSum [.scale 2 (.xlog x dir),.scale (-1) (.xlog (4-x) (-dir)),lin]

def singK (b : Bool) : ℤ := if b then -1 else -3

theorem atomElem_split (terms : ℕ) (z x dir : ℚ) (b : Bool)
    (hx : (b=true ∧ x=4 ∧ dir=-1) ∨ (b=false ∧ x=1 ∧ dir=1)) (u : ℝ) :
    (atomElemExpr terms z x dir).value u=(atomRegExpr terms z x dir b).value u+(singK b:ℝ)*xlog u := by
  rcases hx with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · simp only [atomElemExpr,atomRegExpr,singK,exprSum_value,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,CellExpr.value,↓reduceIte]
    push_cast; ring_nf
  · simp only [atomElemExpr,atomRegExpr,singK,exprSum_value,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,CellExpr.value,Bool.false_eq_true,↓reduceIte]
    push_cast; ring_nf

/-- An atom end cell on `[left,right] ⊂ [1,4]`, expanded at the singular endpoint: `left=1`
forward, `right=4` backwards, in the variable `u ∈ [0,right-left]`. -/
structure AtomCellA where
  left : ℚ
  right : ℚ
  backwards : Bool
  terms : ℕ
  field : CellWitness
  sing : CellWitness
  copies : List SegCopy

def AtomCellA.start (c : AtomCellA) : ℚ := if c.backwards then c.right else c.left
def AtomCellA.dir (c : AtomCellA) : ℚ := if c.backwards then -1 else 1
def AtomCellA.width (c : AtomCellA) : ℚ := c.right-c.left

noncomputable def atomCellA (S G : ℤ) (z : ℚ) (b : BentInput) (ss : List SegSharedI) (c : AtomCellA) :
    Option AtomOut :=
  if 1 ≤ c.left ∧ c.left < c.right ∧ c.right ≤ 4 ∧
      ((c.backwards=true ∧ c.right=4) ∨ (c.backwards=false ∧ c.left=1)) then
    if fieldModelI S (atomRegExpr c.terms z c.start c.dir c.backwards) 0 c.width c.field &&
        tangentI S c.terms c.width c.sing then
      match copySum S (-c.start,0) (-c.dir,0) 0 c.width b.data.segments ss c.copies with
      | some r =>
        let cs := iadd (iadd c.field.coeff (c.sing.coeff.map (fun x => singK c.backwards*x))) r.1
        let err := c.field.remainder+|(singK c.backwards:ℚ)| *c.sing.remainder+r.2
        let bx := modelBox S G cs err 0 c.width
        let line := upperLine (cs.map (fun c : ℤ => (c:ℚ)/S)) c.width err
        some ⟨c.backwards,roundUp G line.1,roundUp G line.2,bx.1,bx.2⟩
      | none => none
    else none
  else none

theorem atomCellA_sound (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (c : AtomCellA) (o : AtomOut) (hc : atomCellA S G z b ss c=some o) :
    (∀ t ∈ Set.Icc ((c.left:ℚ):ℝ) ((c.right:ℚ):ℝ),
      W (z:ℝ) b.data.dual.σ (-(t:ℂ)) ∈ Set.Icc (o.lb:ℝ) (o.ub:ℝ)) ∧
    (∀ u ∈ Set.Icc (0:ℝ) ((c.right-c.left:ℚ):ℝ),
      omega (z:ℝ) (((o.start c.left c.right:ℚ):ℝ)+((o.dir:ℚ):ℝ)*u)-
        2*U b.data.dual.σ (-((((o.start c.left c.right:ℚ):ℝ)+
          ((o.dir:ℚ):ℝ)*u:ℝ):ℂ)) ≤ (o.a:ℝ)+(o.b:ℝ)*u) := by
  unfold atomCellA at hc
  split_ifs at hc with hg hf
  cases hr : copySum S (-c.start,0) (-c.dir,0) 0 c.width b.data.segments ss c.copies with
  | none => simp [hr] at hc
  | some r =>
  simp only [hr,Option.some.injEq] at hc
  subst hc
  have hW0 : (0:ℚ) ≤ c.width := by simp only [AtomCellA.width]; linarith [hg.2.1]
  simp only [Bool.and_eq_true] at hf
  have hF := fieldModelI_sound S _ _ _ _ (by
    unfold atomRegExpr; split <;> simp [exprSum,PositiveSources]) hf.1
  have hT := tangentI_sound S _ _ _ hf.2
  have hpos := (datumCheck_positive b.data dw hd).1
  have hC := copySum_model S hS _ _ 0 c.width hW0 _ ss c.copies r hss hpos hr
  rw [Rat.cast_zero] at hF hC hT
  have hK := modelsOn_smul S (singK c.backwards) _ _ _ _ _ hT
  have hFK := modelsOn_iadd S _ _ _ _ _ _ _ _ hF hK
  have hA := modelsOn_iadd S _ _ _ _ _ _ _ _ hFK hC
  have hanch : (c.backwards=true ∧ c.start=4 ∧ c.dir=-1) ∨ (c.backwards=false ∧ c.start=1 ∧ c.dir=1) := by
    rcases hg.2.2.2 with ⟨hb,h4⟩ | ⟨hb,h4⟩
    · left; simp [AtomCellA.start,AtomCellA.dir,hb,h4]
    · right; simp [AtomCellA.start,AtomCellA.dir,hb,h4]
  have hsum : ModelsOn (atomExpr c.terms z b.data.segments c.start c.dir).value
      (qOf S (iadd (iadd c.field.coeff (c.sing.coeff.map (fun x => singK c.backwards*x))) r.1)) 0 c.width
      (((c.field.remainder+|(singK c.backwards:ℚ)| *c.sing.remainder+r.2):ℚ):ℝ) := by
    have he : (((c.field.remainder+|(singK c.backwards:ℚ)| *c.sing.remainder+r.2):ℚ):ℝ)=
        (c.field.remainder:ℝ)+|((singK c.backwards:ℤ):ℝ)| *(c.sing.remainder:ℝ)+(r.2:ℝ) := by
      push_cast; ring
    rw [he]
    refine ⟨hA.1,hA.2.1,fun u hu => ?_⟩
    have h := hA.2.2 u hu
    simp only at h
    have h0 : (atomExpr c.terms z b.data.segments c.start c.dir).value u=
        (atomElemExpr c.terms z c.start c.dir).value u+(exprSum (b.data.segments.map
          (fun s => CellExpr.scale 2 (.segment s (-c.start,0) (-c.dir,0))))).value u := by
      unfold atomExpr atomElemExpr
      simp only [exprSum_value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        List.map_append,List.sum_append]
      ring
    rw [h0,atomElem_split _ _ _ _ _ hanch u,exprSum_value,List.map_map]
    exact h
  have hbox := modelBox_spec S G hG (iadd (iadd c.field.coeff (c.sing.coeff.map (fun x => singK c.backwards*x))) r.1) (c.field.remainder+|(singK c.backwards:ℚ)| *c.sing.remainder+r.2) 0 c.width _
    (by rw [Rat.cast_zero]; exact hsum)
  rw [Rat.cast_zero] at hbox
  have hl1 : (1:ℝ) ≤ ((c.left:ℚ):ℝ) := by exact_mod_cast hg.1
  have hr4 : ((c.right:ℚ):ℝ) ≤ 4 := by exact_mod_cast hg.2.2.1
  have hw : ((c.width:ℚ):ℝ)=((c.right:ℚ):ℝ)-((c.left:ℚ):ℝ) := by
    simp only [AtomCellA.width,Rat.cast_sub]
  have hin : ∀ u ∈ Set.Icc (0:ℝ) ((c.width:ℚ):ℝ),
      ((c.start:ℚ):ℝ)+((c.dir:ℚ):ℝ)*u ∈ Set.Icc (1:ℝ) 4 := by
    intro u hu
    rw [hw] at hu
    have h1 := hu.1; have h2 := hu.2
    cases hb : c.backwards
    · simp only [AtomCellA.start,AtomCellA.dir,hb,Bool.false_eq_true,↓reduceIte,Rat.cast_one,one_mul]
      constructor <;> linarith
    · simp only [AtomCellA.start,AtomCellA.dir,hb,↓reduceIte,Rat.cast_neg,Rat.cast_one,neg_one_mul]
      constructor <;> linarith
  constructor
  · intro t ht
    have hex : ∃ u ∈ Set.Icc (0:ℝ) ((c.width:ℚ):ℝ), ((c.start:ℚ):ℝ)+((c.dir:ℚ):ℝ)*u=t := by
      rw [hw]
      cases hb : c.backwards
      · refine ⟨t-((c.left:ℚ):ℝ),⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
        simp only [AtomCellA.start,AtomCellA.dir,hb,Bool.false_eq_true,↓reduceIte,Rat.cast_one]; ring
      · refine ⟨((c.right:ℚ):ℝ)-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,?_⟩
        simp only [AtomCellA.start,AtomCellA.dir,hb,↓reduceIte,Rat.cast_neg,Rat.cast_one]; ring
    obtain ⟨u,hu,hut⟩ := hex
    have hv := hbox u hu
    rw [atomExpr_value _ _ hz b.data dw hd _ _ _ (hin u hu)] at hv
    have hcoord : -((((c.start:ℚ):ℝ):ℂ)+(((c.dir:ℚ):ℝ):ℂ)*(u:ℂ))= -(t:ℂ) := by
      rw [← hut,Complex.ofReal_add,Complex.ofReal_mul]
    rw [hut,hcoord] at hv
    rw [W,atom_field_eq_extension]
    exact hv
  · intro u hu
    have hu' : u ∈ Set.Icc (0:ℝ) ((c.width:ℚ):ℝ) := hu
    have hab := abs_le.mp (hsum.2.2 u hu')
    have e : qOf S (iadd (iadd c.field.coeff (c.sing.coeff.map (fun x => singK c.backwards*x))) r.1)=((iadd (iadd c.field.coeff (c.sing.coeff.map (fun x => singK c.backwards*x))) r.1).map (fun c : ℤ => (c:ℚ)/S)).map
        (fun x : ℚ => (x:ℝ)) := by simp [qOf,List.map_map]
    rw [e] at hab
    have hl := upperLine_bound ((iadd (iadd c.field.coeff (c.sing.coeff.map (fun x => singK c.backwards*x))) r.1).map (fun c : ℤ => (c:ℚ)/S)) c.width
      (c.field.remainder+|(singK c.backwards:ℚ)| *c.sing.remainder+r.2) u hu'
    have h1 := Rat.cast_le (K := ℝ) |>.mpr (le_roundUp G hG
      (upperLine ((iadd (iadd c.field.coeff (c.sing.coeff.map (fun x => singK c.backwards*x))) r.1).map (fun c : ℤ => (c:ℚ)/S)) c.width (c.field.remainder+|(singK c.backwards:ℚ)| *c.sing.remainder+r.2)).1)
    have h2 := Rat.cast_le (K := ℝ) |>.mpr (le_roundUp G hG
      (upperLine ((iadd (iadd c.field.coeff (c.sing.coeff.map (fun x => singK c.backwards*x))) r.1).map (fun c : ℤ => (c:ℚ)/S)) c.width (c.field.remainder+|(singK c.backwards:ℚ)| *c.sing.remainder+r.2)).2)
    have hB := mul_le_mul_of_nonneg_right h2 hu.1
    have hval := atomExpr_value c.terms z hz b.data dw hd c.start c.dir u (hin u hu')
    dsimp only
    have hs : (if c.backwards then c.right else c.left)=c.start := rfl
    have hd' : (if c.backwards then (-1:ℚ) else 1)=c.dir := rfl
    simp only [AtomOut.start,AtomOut.dir,hs,hd',Complex.ofReal_add,Complex.ofReal_mul]
    rw [← hval]
    linarith [hab.1,hab.2,hl,h1,hB]

/-- Stored check for an anchored atom cell: same orientation, wider bounds, line above. -/
noncomputable def atomCellAOK (S G : ℤ) (z : ℚ) (b : BentInput) (ss : List SegSharedI) (c : AtomCellA)
    (o : AtomOut) : Bool :=
  match atomCellA S G z b ss c with
  | some o' => decide (o.backwards=c.backwards ∧ c.left < c.right ∧ o.lb ≤ o'.lb ∧ o'.ub ≤ o.ub ∧
      o'.a ≤ o.a ∧ o'.a+o'.b*(c.right-c.left) ≤ o.a+o.b*(c.right-c.left))
  | none => false

theorem atomCellAOK_sound (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (c : AtomCellA) (o : AtomOut) (hc : atomCellAOK S G z b ss c o=true) :
    (∀ t ∈ Set.Icc ((c.left:ℚ):ℝ) ((c.right:ℚ):ℝ),
      W (z:ℝ) b.data.dual.σ (-(t:ℂ)) ∈ Set.Icc (o.lb:ℝ) (o.ub:ℝ)) ∧
    (∀ u ∈ Set.Icc (0:ℝ) ((c.right-c.left:ℚ):ℝ),
      omega (z:ℝ) (((o.start c.left c.right:ℚ):ℝ)+((o.dir:ℚ):ℝ)*u)-
        2*U b.data.dual.σ (-((((o.start c.left c.right:ℚ):ℝ)+
          ((o.dir:ℚ):ℝ)*u:ℝ):ℂ)) ≤ (o.a:ℝ)+(o.b:ℝ)*u) := by
  unfold atomCellAOK at hc
  cases h : atomCellA S G z b ss c with
  | none => simp [h] at hc
  | some o' =>
  simp only [h,decide_eq_true_eq] at hc
  obtain ⟨hb,hlr,hlb,hub,ha,hab⟩ := hc
  have hb' : o'.backwards=c.backwards := by
    unfold atomCellA at h
    split_ifs at h
    split at h
    · simp only [Option.some.injEq] at h; rw [← h]
    · simp at h
  exact atomOut_relax (fun t => W (z:ℝ) b.data.dual.σ (-(t:ℂ)))
    (fun x => omega (z:ℝ) x-2*U b.data.dual.σ (-(x:ℂ))) c.left c.right o o' (by rw [hb,hb'])
    hlr hlb hub ha hab (atomCellA_sound S G hS hG z hz b dw hd ss hss c o' h)

/-- An atom cell: a centred Taylor cell, or an end cell anchored at the singular endpoint `1`
or `4`, both from integer segment copies. -/
inductive AtomCellN
  | taylor (c : AtomCellJ)
  | anchored (c : AtomCellA)

def AtomCellN.left : AtomCellN → ℚ
  | .taylor c => c.left
  | .anchored c => c.left
def AtomCellN.right : AtomCellN → ℚ
  | .taylor c => c.right
  | .anchored c => c.right

instance : AtomProj AtomCellN := ⟨AtomCellN.left,AtomCellN.right⟩

noncomputable def atomCellNOK (S G : ℤ) (z : ℚ) (b : BentInput) (ss : List SegSharedI) :
    AtomCellN → AtomOut → Bool
  | .taylor c, o => atomCellOK S G z b ss c o
  | .anchored c, o => atomCellAOK S G z b ss c o

theorem atomCellNOK_sound (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (c : AtomCellN) (o : AtomOut) (hc : atomCellNOK S G z b ss c o=true) :
    (∀ t ∈ Set.Icc ((AtomProj.left c:ℚ):ℝ) ((AtomProj.right c:ℚ):ℝ),
      W (z:ℝ) b.data.dual.σ (-(t:ℂ)) ∈ Set.Icc (o.lb:ℝ) (o.ub:ℝ)) ∧
    (∀ u ∈ Set.Icc (0:ℝ) ((AtomProj.right c-AtomProj.left c:ℚ):ℝ),
      omega (z:ℝ) (((o.start (AtomProj.left c) (AtomProj.right c):ℚ):ℝ)+((o.dir:ℚ):ℝ)*u)-
        2*U b.data.dual.σ (-((((o.start (AtomProj.left c) (AtomProj.right c):ℚ):ℝ)+
          ((o.dir:ℚ):ℝ)*u:ℝ):ℂ)) ≤ (o.a:ℝ)+(o.b:ℝ)*u) := by
  cases c with
  | taylor c => exact atomCellOK_sound S G hS hG z hz b dw hd ss hss c o hc
  | anchored c => exact atomCellAOK_sound S G hS hG z hz b dw hd ss hss c o hc

/-- All stored atom cells are sound: the per-cell hypotheses of the node assembly. -/
theorem nodeAtomPhysical_of_cells (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0)
    (b : BentInput) (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (cs : List (AtomCellN × AtomOut)) (hcs : ∀ x ∈ cs,atomCellNOK S G z b ss x.1 x.2=true) :
    NodeAtomWPhysical z b cs ∧ NodeAtomLinePhysical z b cs :=
  ⟨fun x hx => (atomCellNOK_sound S G hS hG z hz b dw hd ss hss x.1 x.2 (hcs x hx)).1,
   fun x hx => (atomCellNOK_sound S G hS hG z hz b dw hd ss hss x.1 x.2 (hcs x hx)).2⟩

end CatalanCore.Li2.DecayCert.Seg
