module
public import CatalanCore.Li2.DecayCert.Seg.Ball
public import CatalanCore.Li2.DecayCert.Seg.NodeDefs
public import CatalanCore.Li2.DecayCert.Covers.Physical
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

/-- The fused field model on `[0,width]` at scale `S`: compile, round, check. -/
noncomputable def fieldModelI (S : ℤ) (x : CellExpr) (R : ℚ) (w : CellWitness) : Bool :=
  match LatticeGate.compileFast (-R) R x w.model with
  | none => false
  | some m => decide (0 ≤ R) && coefficientCheck S m w && remainderCheck S (max |-R| |R|) m w

theorem fieldModelI_sound (S : ℤ) (x : CellExpr) (R : ℚ) (w : CellWitness)
    (hp : PositiveSources x) (hc : fieldModelI S x R w=true) :
    ModelsOn x.value (qOf S w.coeff) (-(R:ℝ)) R w.remainder := by
  unfold fieldModelI at hc
  split at hc
  · contradiction
  rename_i m hm
  rw [LatticeGate.compileFast_eq] at hm
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0,hco⟩,hrm⟩ := hc
  have hR := of_decide_eq_true h0
  have h := roundModel_sound S (-R) R m w x.value
    (compileModel_sound (-R) R x w.model m (by linarith) hp hm) hco hrm
  have e : (gridCoeffs S w).map (fun q : ℚ => (q:ℝ))=qOf S w.coeff := by
    simp [gridCoeffs,qOf,List.map_map]
  rw [e,Rat.cast_neg] at h
  exact h

/-- One segment copy: a disc copy from the integer evaluator, or the segment's own polynomial
model (`.segOwn` witness) when the cell lies on the segment. -/
inductive SegCopy
  | disc (w : CopyI)
  | own (w : CellWitness)

noncomputable def copyOne (S : ℤ) (s : SegSharedI) (d : QSegment) (p e : CQ) (R : ℚ) :
    SegCopy → Option (List ℤ×ℚ)
  | .disc w => match ballCopyJ S s d p e R w with
    | some o => some (o.1,(o.2:ℚ)/S)
    | none => none
  | .own w => if fieldModelI S (.segment d p e) R w then some (w.coeff,w.remainder) else none

theorem copyOne_model (S : ℤ) (hS : 0 < S) (s : SegSharedI) (d : QSegment) (hsh : s.ok S d=true)
    (p e : CQ) (R : ℚ) (w : SegCopy) (o : List ℤ×ℚ)
    (hpos : ∀ x ∈ Set.Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hc : copyOne S s d p e R w=some o) :
    ModelsOn (CellExpr.segment d p e).value (qOf S o.1) (-(R:ℝ)) R o.2 := by
  cases w with
  | disc w =>
    simp only [copyOne] at hc
    cases ho : ballCopyJ S s d p e R w with
    | none => simp [ho] at hc
    | some o' =>
    simp only [ho,Option.some.injEq] at hc
    subst hc
    have hm := ballCopyJ_model S hS s d hsh p e R w o' hpos ho
    have hR : (0:ℝ) ≤ R := hm.1
    have := hm.onIcc (-(R:ℝ)) R (by linarith) (fun u hu => abs_le.mpr hu)
    simpa [qOf] using this
  | own w =>
    simp only [copyOne] at hc
    split_ifs at hc with hf
    simp only [Option.some.injEq] at hc
    subst hc
    exact fieldModelI_sound S _ R w hpos hf

/-- The doubled copies of all segments, summed. -/
noncomputable def copySum (S : ℤ) (p e : CQ) (R : ℚ) : List QSegment → List SegSharedI → List SegCopy →
    Option (List ℤ×ℚ)
  | [], [], [] => some ([],0)
  | d::ds, s::ss, w::ws => do
      let o ← copyOne S s d p e R w
      let r ← copySum S p e R ds ss ws
      pure (iadd (o.1.map (fun c => 2*c)) r.1,2*o.2+r.2)
  | _, _, _ => none

def sharedOK (S : ℤ) : List QSegment → List SegSharedI → Bool
  | [], [] => true
  | d::ds, s::ss => s.ok S d && sharedOK S ds ss
  | _, _ => false

theorem copySum_model (S : ℤ) (hS : 0 < S) (p e : CQ) (R : ℚ) (hR : 0 ≤ R) :
    ∀ (ds : List QSegment) (ss : List SegSharedI) (ws : List SegCopy) (r : List ℤ×ℚ),
    sharedOK S ds ss=true →
    (∀ d ∈ ds,∀ x ∈ Set.Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x) →
    copySum S p e R ds ss ws=some r →
    ModelsOn (fun u => (ds.map (fun d => 2*(CellExpr.segment d p e).value u)).sum) (qOf S r.1)
      (-(R:ℝ)) R r.2 := by
  have hRr : (0:ℝ) ≤ R := by exact_mod_cast hR
  intro ds
  induction ds with
  | nil =>
    intro ss ws r _ _ h
    rcases ss with _|⟨s,ss⟩ <;> rcases ws with _|⟨w,ws⟩ <;> simp [copySum] at h
    subst h
    refine ⟨by linarith,by simp,fun u _ => ?_⟩
    simp [qOf,evalModel_nil]
  | cons d ds ih =>
    intro ss ws r hok hpos h
    rcases ss with _|⟨s,ss⟩ <;> rcases ws with _|⟨w,ws⟩
    · simp [copySum] at h
    · simp [copySum] at h
    · simp [copySum] at h
    simp only [sharedOK,Bool.and_eq_true] at hok
    simp only [copySum] at h
    cases ho : copyOne S s d p e R w with
    | none => simp [ho] at h
    | some o =>
    cases hr : copySum S p e R ds ss ws with
    | none => simp [ho,hr] at h
    | some r' =>
    simp only [ho,hr,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.some.injEq] at h
    subst h
    have hm1 := copyOne_model S hS s d hok.1 p e R w o (hpos d List.mem_cons_self) ho
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

/-- Bounds of an integer polynomial model on `[-R,R]`, rounded outward to the grid `1/G`. -/
def modelBox (S G : ℤ) (cs : List ℤ) (err R : ℚ) : QBox :=
  let a := cs.map (fun c : ℤ => (c:ℚ)/S)
  (roundDn G (polyLBQ a (-R) R-err),roundUp G (polyUBQ a (-R) R+err))

theorem modelBox_spec (S G : ℤ) (hG : 0 < G) (cs : List ℤ) (err R : ℚ) (f : ℝ → ℝ)
    (hm : ModelsOn f (qOf S cs) (-(R:ℝ)) R err) :
    ∀ u ∈ Set.Icc (-(R:ℝ)) (R:ℝ),f u ∈ Set.Icc ((modelBox S G cs err R).1:ℝ)
      ((modelBox S G cs err R).2:ℝ) := by
  have e : qOf S cs=(cs.map (fun c : ℤ => (c:ℚ)/S)).map (fun x : ℚ => (x:ℝ)) := by
    simp [qOf,List.map_map]
  rw [e] at hm
  intro u hu
  have hm' : ModelsOn f ((cs.map (fun c : ℤ => (c:ℚ)/S)).map (fun x : ℚ => (x:ℝ)))
      ((-R:ℚ):ℝ) (R:ℝ) err := by rw [Rat.cast_neg]; exact hm
  have h := cell_ub_lb f _ (-R) R err hm' u (by rw [Rat.cast_neg]; exact hu)
  have h1 : ((roundDn G (polyLBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) (-R) R-err):ℚ):ℝ) ≤
      ((polyLBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) (-R) R-err:ℚ):ℝ) := Rat.cast_le.mpr (roundDn_le G hG _)
  have h2 : ((polyUBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) (-R) R+err:ℚ):ℝ) ≤
      ((roundUp G (polyUBQ (cs.map (fun c : ℤ => (c:ℚ)/S)) (-R) R+err):ℚ):ℝ) :=
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
        (edgeDirection b c.edge)) c.rad c.field then
      match copySum S (cqAdd (edgeOrigin b c.edge) (cqScale c.mid (edgeDirection b c.edge)))
          (edgeDirection b c.edge) c.rad b.data.segments ss c.copies with
      | some r => some (modelBox S G (iadd c.field.coeff r.1) (c.field.remainder+r.2) c.rad)
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
  cases hr : copySum S p e c.rad b.data.segments ss c.copies with
  | none => simp [hr] at hc
  | some r =>
  simp only [hr,Option.some.injEq] at hc
  subst hc
  have hR0 : (0:ℚ) ≤ c.rad := by simp only [ContourCellJ.rad]; linarith [hg.2.2.1]
  have hF := fieldModelI_sound S _ _ _ (positive_fieldExpr _ _ _ _) hf
  have hpos := (datumCheck_positive b.data dw hd).1
  have hC := copySum_model S hS p e c.rad hR0 _ ss c.copies r hss hpos hr
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
  have hbox := modelBox_spec S G hG _ _ _ _ hsum
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
  | .holder c => contourBounds z b c

theorem contourCellN_sound (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (c : ContourCellN) (B : QBox) (hc : contourCellN S G z b ss c=some B) :
    ∀ t ∈ Set.Icc ((ContourProj.left c:ℚ):ℝ) ((ContourProj.right c:ℚ):ℝ),
      W (z:ℝ) b.data.dual.σ (cqReal (edgeOrigin b (ContourProj.edge c))+
        cqReal (edgeDirection b (ContourProj.edge c))*(t:ℂ)) ∈ Set.Icc (B.1:ℝ) (B.2:ℝ) := by
  cases c with
  | taylor c => exact contourCellJ_sound S G hS hG z hz b dw hd ss hss c B hc
  | holder c => exact contourBounds_physical z hz b dw hd c B hc

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
    if fieldModelI S (atomElemExpr c.terms z c.mid 1) c.rad c.field then
      match copySum S (-c.mid,0) (-1,0) c.rad b.data.segments ss c.copies with
      | some r =>
        let cs := iadd c.field.coeff r.1
        let err := c.field.remainder+r.2
        let bx := modelBox S G cs err c.rad
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
  cases hr : copySum S (-c.mid,0) (-1,0) c.rad b.data.segments ss c.copies with
  | none => simp [hr] at hc
  | some r =>
  simp only [hr,Option.some.injEq] at hc
  subst hc
  have hR0 : (0:ℚ) ≤ c.rad := by simp only [AtomCellJ.rad]; linarith [hg.2.1]
  have hF := fieldModelI_sound S _ _ _ (by
    simp [atomElemExpr,exprSum,PositiveSources]) hf
  have hpos := (datumCheck_positive b.data dw hd).1
  have hC := copySum_model S hS _ _ c.rad hR0 _ ss c.copies r hss hpos hr
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
  have hbox := modelBox_spec S G hG _ _ _ _ hsum
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
  have hs := atomCellJ_sound S G hS hG z hz b dw hd ss hss c o' h
  have hb' : o'.backwards=false := by
    unfold atomCellJ at h
    split_ifs at h
    split at h
    · simp only [Option.some.injEq] at h; rw [← h]
    · simp at h
  refine ⟨fun t ht => ?_,fun u hu => ?_⟩
  · have hw := hs.1 t ht
    have h1 : (o.lb:ℝ) ≤ o'.lb := by exact_mod_cast hlb
    have h2 : (o'.ub:ℝ) ≤ o.ub := by exact_mod_cast hub
    exact ⟨h1.trans hw.1,hw.2.trans h2⟩
  · have hw := hs.2 u hu
    have hst : o.start c.left c.right=o'.start c.left c.right := by simp [AtomOut.start,hb,hb']
    have hdir : o.dir=o'.dir := by simp [AtomOut.dir,hb,hb']
    rw [hst,hdir]
    refine hw.trans ?_
    have hwpos : (0:ℝ) < ((c.right-c.left:ℚ):ℝ) := by
      have : (0:ℚ) < c.right-c.left := by linarith
      exact_mod_cast this
    have ha' : (o'.a:ℝ) ≤ o.a := by exact_mod_cast ha
    have hab' : (o'.a:ℝ)+(o'.b:ℝ)*((c.right-c.left:ℚ):ℝ) ≤ (o.a:ℝ)+(o.b:ℝ)*((c.right-c.left:ℚ):ℝ) := by
      exact_mod_cast hab
    set w : ℝ := ((c.right-c.left:ℚ):ℝ)
    have hu0 := hu.1; have hu1 := hu.2
    have key : ((o.a:ℝ)+(o.b:ℝ)*u-((o'.a:ℝ)+(o'.b:ℝ)*u))*w=
        (w-u)*((o.a:ℝ)-(o'.a:ℝ))+u*(((o.a:ℝ)+(o.b:ℝ)*w)-((o'.a:ℝ)+(o'.b:ℝ)*w)) := by ring
    have hnn : 0 ≤ ((o.a:ℝ)+(o.b:ℝ)*u-((o'.a:ℝ)+(o'.b:ℝ)*u))*w := by
      rw [key]; exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hu0 (by linarith))
    have := nonneg_of_mul_nonneg_left hnn hwpos
    linarith

/-- All stored atom cells are sound: the per-cell hypotheses of the node assembly. -/
theorem nodeAtomPhysical_of_cells (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0)
    (b : BentInput) (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (ss : List SegSharedI) (hss : sharedOK S b.data.segments ss=true)
    (cs : List (AtomCellJ × AtomOut)) (hcs : ∀ x ∈ cs,atomCellOK S G z b ss x.1 x.2=true) :
    NodeAtomWPhysical z b cs ∧ NodeAtomLinePhysical z b cs :=
  ⟨fun x hx => (atomCellOK_sound S G hS hG z hz b dw hd ss hss x.1 x.2 (hcs x hx)).1,
   fun x hx => (atomCellOK_sound S G hS hG z hz b dw hd ss hss x.1 x.2 (hcs x hx)).2⟩

end CatalanCore.Li2.DecayCert.Seg
