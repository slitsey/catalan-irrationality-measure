module
public import CatalanCore.Li2.DecayCert.Simple.Bridge
public import CatalanCore.Li2.DecayCert.Lattice.Simple.Pattern
public import CatalanCore.Li2.DecayCert.Covers.LinePartition
public import CatalanCore.Li2.DecayCert.Lattice.Chain
/-! The `[0, Y]` part of the lattice penalty from passed TC cells. `WLink` bundles the source
identifications of a datum. A `WSide` is a sign pattern on `[0, Y]`, one chain of sign cells per gap away
from the roots and one root cell per root. `WSide.signAway` gives `W - θ` the pattern's sign away from the
roots, and `WSide.penalty` bounds `∫₀^Y (W - θ)₊` by the positive-gap integrals plus the root-cell error
(`signPattern_bound`). `primBoxF` encloses the lattice primitive at a rational point, and
`gapIntegral_le` bounds the integral of `W - θ` over a gap of `[0, Y]` from two such boxes. `RSide.penalty` bounds `∫_Y^C (W - θ)₊` by a chain of Right cells. -/
@[expose] public section
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Li2.DecayCert CatalanCore.Li2.Decay CatalanCore.Li2.DecayCert.LatticeSimple
noncomputable section

/-- The source identifications a W cell needs, bundled once per datum. -/
structure WLink (s : SourceF) (logs : List LogEntry) (r : SourceR) (z θ Y : ℝ) (σ1 σ2 : Measure ℂ)
    [IsFiniteMeasure σ2] (d : LatticeMomentData σ1 σ2 Y) (K : ℕ) : Prop where
  logs : LogsOK logs
  enc : SourceEnc s r
  hY : 0<Y
  hL : r.L=Real.log |z|
  hθ : (s.theta:ℝ)=θ
  hy0 : (s.y0:ℝ)=d.y0
  hYs : (s.Y:ℝ)=Y
  hM2 : r.M2=σ2.real univ
  hU1c : r.U1c=d.c 0*Real.log (4/Y)
  hq1 : ∀ x : ℝ, hornerR (2*x/Y-1) r.q1=(ownUPoly d).eval x
  hK : s.MU.length=K
  hw : ∀ k, r.w k=(moment σ2 (d.y0:ℂ) (k+1)).re/((k+1:ℕ):ℝ)
  hglob : 2*mpErr (σ2.real univ) (d.supportRadius/(-d.y0)) K ≤ dec S s.globalW


/-- On a WOrigin cell the TC target leaves out `−2 x log x`, which the hull bounds. -/
theorem approxFieldO_eq_target (s : SourceF) (r : SourceR) (p : TCSpec) (hk : p.kind=.WOrigin)
    (z θ Y : ℝ) (σ1 σ2 : Measure ℂ) (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (hL : r.L=Real.log |z|) (hθ : (s.theta:ℝ)=θ) (hy0 : (s.y0:ℝ)=d.y0) (hYs : (s.Y:ℝ)=Y)
    (hM2 : r.M2=σ2.real univ) (hU1c : r.U1c=d.c 0*Real.log (4/Y))
    (hq1 : ∀ x : ℝ, hornerR (2*x/Y-1) r.q1=(ownUPoly d).eval x) (hK : s.MU.length=K)
    (hw : ∀ k, r.w k=(moment σ2 (d.y0:ℂ) (k+1)).re/((k+1:ℕ):ℝ))
    (hY : 0 < Y) (u : ℝ) (hpos : 0 ≤ (p.center:ℝ)+u) :
    latticeApproxField z θ d K ((p.center:ℝ)+u)=tcTargetR s r p u+(-2*xlog ((p.center:ℝ)+u)) := by
  have hy := d.y0_neg
  have hd : 0 < (p.center:ℝ)+u-d.y0 := by linarith
  have hW : tcIsW p=true := by simp [tcIsW,hk]
  have hR : p.kind ≠ .Right := by rw [hk]; decide
  simp only [tcTargetR,hW,if_true,wModelR,wConstR,hR,if_false,tcArgs,hk,xlogSumR]
  simp only [show (TCKind.WOrigin==TCKind.WOrigin)=true by decide,if_true,
    List.nil_append,List.cons_append,List.append_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  rw [latticeApproxField,V_real_value,phi0_real_closed,LatticeMomentData.mpValue,mp_real,← hq1]
  have ht : (((p.center/(s.Y/2)-1:ℚ):ℝ)+((1/(s.Y/2):ℚ):ℝ)*u)=2*((p.center:ℝ)+u)/Y-1 := by
    have hY0 : Y ≠ 0 := hY.ne'
    push_cast; rw [hYs]; field_simp; ring
  rw [ht,abs_of_pos hd]
  have hcy : (((p.center-s.y0:ℚ):ℝ)+u)=(p.center:ℝ)+u-d.y0 := by push_cast; rw [hy0]; ring
  rw [hcy,hL,hθ,hM2,hU1c,hK]
  have hsum : ∑ k ∈ Finset.range K,r.w k*((p.center:ℝ)+u-d.y0)^(-((k+1:ℕ):ℤ))=
      ∑ k ∈ Finset.range K,(moment σ2 (d.y0:ℂ) (k+1)).re/(((k+1:ℕ):ℝ)*((p.center:ℝ)+u-d.y0)^(k+1)) := by
    apply Finset.sum_congr rfl; intro k _
    rw [hw,zpow_neg,zpow_natCast]; field_simp
  rw [hsum]
  simp only [xlog]; push_cast; ring

theorem tcCheck_origin_params (s : SourceF) (logs : List LogEntry) (p : TCSpec) (lower upper : ℤ)
    (pos : Option Bool) (hc : tcCheck s logs p lower upper pos=true) (hk : p.kind=.WOrigin) :
    p.left=0 ∧ 0 < p.right ∧ p.right ≤ 1/3 := by
  by_contra hcon
  have hcond : p.left≠0 ∨ p.right≤0 ∨ 1/3<p.right := by
    by_contra h2; push_neg at h2; exact hcon ⟨h2.1,h2.2.1,h2.2.2⟩
  have hO : ∀ lg c, originF lg p c=none := by
    intro lg c
    simp only [originF,hk,show (TCKind.WOrigin==TCKind.WOrigin)=true by decide,if_true]
    rw [if_pos hcond]
  have hP : ∀ lg R, wPartF s lg p R=none := by intro lg R; simp [wPartF,hO]
  have hW : tcIsW p=true := by simp [tcIsW,hk]
  unfold tcCheck at hc
  simp [buildTCBox,hW,hP] at hc

/-- A passed WOrigin cell encloses `W − θ` on its interval `[0, right]`. -/
theorem wOriginCell_bound (s : SourceF) (logs : List LogEntry) (p : TCSpec) (lower upper : ℤ)
    (pos : Option Bool) (hc : tcCheck s logs p lower upper pos=true) (r : SourceR) (z θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ2] (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (lk : WLink s logs r z θ Y σ1 σ2 d K) (hk : p.kind=.WOrigin)
    (x : ℝ) (hx : (p.left:ℝ) ≤ x ∧ x ≤ p.right) :
    dec S lower ≤ W z (σ1+σ2) (x:ℂ)-θ ∧ W z (σ1+σ2) (x:ℂ)-θ ≤ dec S upper := by
  have hg := tcCheck_geom s logs p lower upper pos hc
  have hpr := tcCheck_origin_params s logs p lower upper pos hc hk
  simp only [tcGeometryCheck,Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨h0,hYb⟩,-⟩,-⟩,-⟩,-⟩ := hg
  obtain ⟨hr0,hlr,hcl,hrc,-⟩ := of_decide_eq_true h0
  have hwb : (p.kind==.W || p.kind==.WOrigin)=true := by simp [hk]
  rw [hwb,Bool.not_true,Bool.false_or] at hYb
  have hrY := (of_decide_eq_true hYb).2
  have hl0 : (p.left:ℝ)=0 := by exact_mod_cast hpr.1
  have hr13 : (p.right:ℝ) ≤ 1/3 := by
    rw [show (1/3:ℝ)=((1/3:ℚ):ℝ) by norm_num]; exact_mod_cast hpr.2.2
  have hcl' : (p.center:ℝ)-p.radius ≤ p.left := by exact_mod_cast hcl
  have hrc' : (p.right:ℝ) ≤ p.center+p.radius := by exact_mod_cast hrc
  have hrY' : (p.right:ℝ) ≤ Y := by rw [← lk.hYs]; exact_mod_cast hrY
  have hW : tcIsW p=true := by simp [tcIsW,hk]
  have hx0 : 0 ≤ x := by rw [← hl0]; exact hx.1
  set u := x-(p.center:ℝ) with hu_def
  have hxu : x=(p.center:ℝ)+u := by rw [hu_def]; ring
  have hu : |u| ≤ (p.radius:ℝ) := abs_le.mpr ⟨by linarith,by linarith⟩
  let e : ℝ → ℝ := fun v => if 0 ≤ (p.center:ℝ)+v then
    -2*(U σ2 ((((p.center:ℝ)+v:ℝ)):ℂ)-d.mpValue K ((p.center:ℝ)+v)) else 0
  have he : ∀ v, |v| ≤ (p.radius:ℝ) → |e v| ≤ dec S (if tcIsW p then s.globalW else s.globalA) := by
    intro v _
    rw [if_pos hW]
    by_cases h0 : 0 ≤ (p.center:ℝ)+v
    · simp only [e,if_pos h0,abs_mul,abs_neg,abs_two]
      exact (mul_le_mul_of_nonneg_left (second_mp_err Y σ1 σ2 d K _ h0) (by norm_num)).trans lk.hglob
    · simp only [e,if_neg h0,abs_zero]
      exact (mul_nonneg (by norm_num)
        ((abs_nonneg _).trans (second_mp_err Y σ1 σ2 d K 0 le_rfl))).trans lk.hglob
  have hm := xlog_ge_end x (p.right:ℝ) hx0 hx.2 hr13
  have hn : xlog x ≤ 0 := Real.mul_log_nonpos hx0 (by linarith [hx.2])
  have hH : (0:ℝ) ≤ -2*xlog x ∧ -2*xlog x ≤ hullBoundR p := by
    simp only [hullBoundR,hW,if_true,originBoundR,hk,if_true]
    unfold xlog at hm hn ⊢
    constructor <;> linarith
  have key := tcCheck_sound s logs p lower upper pos hc r lk.logs lk.enc (-2*xlog x) hH e he u hu
  have hx0' : 0 ≤ (p.center:ℝ)+u := by rw [← hxu]; exact hx0
  have ht := approxFieldO_eq_target s r p hk z θ Y σ1 σ2 d K lk.hL lk.hθ lk.hy0 lk.hYs lk.hM2 lk.hU1c
    lk.hq1 lk.hK lk.hw lk.hY u hx0'
  have hf := W_field_eq z θ Y lk.hY σ1 σ2 d K x ⟨hx0,hx.2.trans hrY'⟩
  have heq : tcTargetR s r p u+(-2*xlog x)+e u=W z (σ1+σ2) (x:ℂ)-θ := by
    rw [hf,hxu,ht]; simp only [e,if_pos hx0']; ring
  rw [heq] at key
  exact ⟨key.1,key.2.1⟩

/-- A stored W cell: its spec, its claimed integer range and its sign claim. -/
structure WCell where
  spec : TCSpec
  lower : ℤ
  upper : ℤ
  pos : Option Bool

def WCell.ok (s : SourceF) (logs : List LogEntry) (c : WCell) : Bool :=
  (c.spec.kind==.W || c.spec.kind==.WOrigin) && tcCheck s logs c.spec c.lower c.upper c.pos

def WCell.iv (c : WCell) : QInterval := ⟨c.spec.left,c.spec.right⟩

theorem tcCheck_sign (s : SourceF) (logs : List LogEntry) (p : TCSpec) (lower upper : ℤ)
    (pos : Option Bool) (hc : tcCheck s logs p lower upper pos=true) :
    (pos=some true → 0 ≤ lower) ∧ (pos=some false → upper ≤ 0) := by
  unfold tcCheck at hc
  cases hb : buildTCBox s logs p with
  | none => rw [hb] at hc; simp at hc
  | some m =>
    rw [hb] at hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨-,hs⟩ := hc
    constructor
    · intro h; subst h; simpa using hs
    · intro h; subst h; simpa using hs

theorem WCell.bound (s : SourceF) (logs : List LogEntry) (r : SourceR) (z θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ2] (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (lk : WLink s logs r z θ Y σ1 σ2 d K) (c : WCell) (hc : c.ok s logs=true)
    (x : ℝ) (hx : (c.spec.left:ℝ) ≤ x ∧ x ≤ c.spec.right) :
    dec S c.lower ≤ W z (σ1+σ2) (x:ℂ)-θ ∧ W z (σ1+σ2) (x:ℂ)-θ ≤ dec S c.upper := by
  simp only [WCell.ok,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at hc
  rcases hc.1 with hk|hk
  · exact wCell_bound s logs c.spec c.lower c.upper c.pos hc.2 r lk.logs lk.enc hk z θ Y lk.hY σ1 σ2 d K
      lk.hL lk.hθ lk.hy0 lk.hYs lk.hM2 lk.hU1c lk.hq1 lk.hK lk.hw lk.hglob x hx
  · exact wOriginCell_bound s logs c.spec c.lower c.upper c.pos hc.2 r z θ Y σ1 σ2 d K lk hk x hx

theorem dec_nonneg_of (a : ℤ) (h : 0 ≤ a) : 0 ≤ dec S a := by
  unfold dec; exact div_nonneg (by exact_mod_cast h) (by unfold S; positivity)

theorem dec_nonpos_of (a : ℤ) (h : a ≤ 0) : dec S a ≤ 0 := by
  unfold dec; exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) (by unfold S; positivity)

/-- A passed sign cell has the claimed sign of `W - θ` on its interval. -/
theorem WCell.sign (s : SourceF) (logs : List LogEntry) (r : SourceR) (z θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ2] (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (lk : WLink s logs r z θ Y σ1 σ2 d K) (c : WCell) (hc : c.ok s logs=true) (b : Bool)
    (hpos : c.pos=some b)
    (x : ℝ) (hx : (c.spec.left:ℝ) ≤ x ∧ x ≤ c.spec.right) :
    if b then 0 ≤ W z (σ1+σ2) (x:ℂ)-θ else W z (σ1+σ2) (x:ℂ)-θ ≤ 0 := by
  have hbd := c.bound s logs r z θ Y σ1 σ2 d K lk hc x hx
  have hc' := hc
  simp only [WCell.ok,Bool.and_eq_true] at hc'
  have hsg := tcCheck_sign s logs c.spec c.lower c.upper c.pos hc'.2
  cases b
  · simp only [Bool.false_eq_true,if_false]
    exact hbd.2.trans (dec_nonpos_of _ (hsg.2 hpos))
  · simp only [if_true]
    exact (dec_nonneg_of _ (hsg.1 hpos)).trans hbd.1

/-- The away interval of gap `i` of a pattern on `[a, b]`: the gap minus its root cells. -/
def _root_.CatalanCore.Li2.DecayCert.LatticeSimple.Pattern.awayLo (s : Pattern) (i : ℕ) : ℚ := if i=0 then s.node 0 else s.node i+s.delta i
def _root_.CatalanCore.Li2.DecayCert.LatticeSimple.Pattern.awayHi (s : Pattern) (i : ℕ) : ℚ := if i+1=s.gaps then s.node s.gaps else s.node (i+1)-s.delta (i+1)

/-- A side of the penalty on `[a, b]`: a sign pattern, one chain of sign cells per gap away from the
roots, and one root cell per root. The W side (`[0, Y]`) and the atom side (`[1, 4]`) are instances. -/
structure Side where
  pat : Pattern
  away : List (List WCell)
  roots : List WCell

/-- The structural check of a side, for a cell check `ok`. -/
def Side.check (ok : WCell → Bool) (a b : ℚ) (w : Side) : Bool :=
  w.pat.check a b && decide (w.away.length=w.pat.gaps ∧ w.roots.length=w.pat.gaps-1) &&
  (List.range w.pat.gaps).all (fun i => match w.away[i]? with
    | some cs => decide (w.pat.awayLo i < w.pat.awayHi i) && chainCheck (w.pat.awayLo i) (w.pat.awayHi i) (cs.map WCell.iv) &&
        cs.all (fun c => ok c && decide (c.pos=some (w.pat.positive i)))
    | none => false) &&
  (List.range (w.pat.gaps-1)).all (fun i => match w.roots[i]? with
    | some c => ok c && decide (c.spec.left ≤ w.pat.node (i+1)-w.pat.delta (i+1) ∧
        w.pat.node (i+1)+w.pat.delta (i+1) ≤ c.spec.right)
    | none => false)

theorem Side.check_parts (ok : WCell → Bool) (a b : ℚ) (w : Side) (hw : w.check ok a b=true) :
    w.pat.check a b=true ∧
    (∀ i, i < w.pat.gaps → ∃ cs, w.away[i]?=some cs ∧ w.pat.awayLo i < w.pat.awayHi i ∧
      chainCheck (w.pat.awayLo i) (w.pat.awayHi i) (cs.map WCell.iv)=true ∧
      ∀ c ∈ cs, ok c=true ∧ c.pos=some (w.pat.positive i)) ∧
    (∀ i, i < w.pat.gaps-1 → ∃ c, w.roots[i]?=some c ∧ ok c=true ∧
      c.spec.left ≤ w.pat.node (i+1)-w.pat.delta (i+1) ∧ w.pat.node (i+1)+w.pat.delta (i+1) ≤ c.spec.right) := by
  simp only [Side.check,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hw
  obtain ⟨⟨⟨hp,-⟩,ha⟩,hr⟩ := hw
  refine ⟨hp,?_,?_⟩
  · intro i hi
    have h := ha i hi
    cases hc : w.away[i]? with
    | none => rw [hc] at h; simp at h
    | some cs =>
      rw [hc] at h
      simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
      exact ⟨cs,rfl,h.1.1,h.1.2,fun c hc' => ⟨(h.2 c hc').1,(h.2 c hc').2⟩⟩
  · intro i hi
    have h := hr i hi
    cases hc : w.roots[i]? with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h
      exact ⟨c,rfl,h.1,h.2.1,h.2.2⟩

/-- Passed sign cells give `f` its pattern's sign away from the root cells. -/
theorem Side.signAway (ok : WCell → Bool) (a b : ℚ) (w : Side) (hw : w.check ok a b=true) (f : ℝ → ℝ)
    (hsign : ∀ c, ok c=true → ∀ bb, c.pos=some bb → ∀ x, (c.spec.left:ℝ) ≤ x ∧ x ≤ c.spec.right →
      if bb then 0 ≤ f x else f x ≤ 0) :
    (w.pat.toSignPartition a b (w.check_parts ok a b hw).1).signAway f := by
  obtain ⟨hp,ha,-⟩ := w.check_parts ok a b hw
  intro i hi x hx hnot
  change i < w.pat.gaps at hi
  change x ∈ Icc (w.pat.node i:ℝ) (w.pat.node (i+1):ℝ) at hx
  change if w.pat.positive i then 0 ≤ f x else f x ≤ 0
  obtain ⟨cs,-,hlt,hch,hcs⟩ := ha i hi
  have hlo : (w.pat.awayLo i:ℝ) ≤ x := by
    unfold LatticeSimple.Pattern.awayLo
    split_ifs with h0
    · subst h0; exact hx.1
    · have hn := hnot ⟨i-1,by change i-1 < w.pat.gaps-1; omega⟩
      have he : i-1+1=i := by omega
      simp only [SignPartition.rootCell,LatticeSimple.Pattern.toSignPartition,he,mem_Icc,not_and_or,not_le] at hn
      push_cast
      rcases hn with hn|hn
      · linarith [hx.1]
      · exact hn.le
  have hhi : x ≤ (w.pat.awayHi i:ℝ) := by
    unfold LatticeSimple.Pattern.awayHi
    split_ifs with h0
    · rw [← h0]; exact hx.2
    · have hn := hnot ⟨i,by change i < w.pat.gaps-1; omega⟩
      simp only [SignPartition.rootCell,LatticeSimple.Pattern.toSignPartition,mem_Icc,not_and_or,not_le] at hn
      push_cast
      rcases hn with hn|hn
      · exact hn.le
      · linarith [hx.2]
  have hcov := chainCheck_closed_cover _ _ _ hlt hch
  have hxm : x ∈ Icc (w.pat.awayLo i:ℝ) (w.pat.awayHi i:ℝ) := ⟨hlo,hhi⟩
  rw [hcov] at hxm
  simp only [mem_iUnion,List.mem_map] at hxm
  obtain ⟨iv,⟨c,hc,rfl⟩,hxc⟩ := hxm
  exact hsign c (hcs c hc).1 _ (hcs c hc).2 x hxc

/-- Root-cell bounds `ep i ≥ sup f` and `em i ≥ sup (−f)`, as rationals. -/
def Side.ep (w : Side) (i : ℕ) : ℚ := match w.roots[i]? with
  | some c => max ((c.upper:ℚ)/(S:ℚ)) 0 | none => 0
def Side.em (w : Side) (i : ℕ) : ℚ := match w.roots[i]? with
  | some c => max (-(c.lower:ℚ)/(S:ℚ)) 0 | none => 0

theorem dec_eq_ratCast (a : ℤ) : dec S a=(((a:ℚ)/(S:ℚ):ℚ):ℝ) := by
  unfold dec; push_cast; rfl

/-- A side's penalty: `∫_a^b f₊` is at most the pattern's positive-gap caps plus the root-cell error. -/
theorem Side.penalty (ok : WCell → Bool) (a b : ℚ) (w : Side) (hw : w.check ok a b=true) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (a:ℝ) (b:ℝ)))
    (hbound : ∀ c, ok c=true → ∀ x, (c.spec.left:ℝ) ≤ x ∧ x ≤ c.spec.right →
      dec S c.lower ≤ f x ∧ f x ≤ dec S c.upper)
    (hsign : ∀ c, ok c=true → ∀ bb, c.pos=some bb → ∀ x, (c.spec.left:ℝ) ≤ x ∧ x ≤ c.spec.right →
      if bb then 0 ≤ f x else f x ≤ 0)
    (cap : ℕ → ℚ)
    (hcap : ∀ i, i < w.pat.gaps → w.pat.positive i=true →
      (∫ x in (w.pat.node i:ℝ)..(w.pat.node (i+1):ℝ), f x) ≤ (cap i:ℝ))
    (total : ℚ) (hscalar : decide (w.pat.plusCap cap+w.pat.rootCap w.ep w.em ≤ total)=true) :
    (∫ x in (a:ℝ)..(b:ℝ), pos (f x)) ≤ (total:ℝ) := by
  obtain ⟨hp,-,hr⟩ := w.check_parts ok a b hw
  have hpp := w.pat.check_parts a b hp
  have hab : a ≤ b := by
    have := hpp.2.1 0 w.pat.gaps hpp.1.1 le_rfl
    rw [hpp.1.2.1,hpp.1.2.2] at this; exact this.le
  have hroot : ∀ i : Fin (w.pat.gaps-1), ∀ x ∈ (w.pat.toSignPartition a b hp).rootCell i,
      dec S (match w.roots[(i:ℕ)]? with | some c => c.lower | none => 0) ≤ f x ∧
      f x ≤ dec S (match w.roots[(i:ℕ)]? with | some c => c.upper | none => 0) := by
    intro i x hx
    obtain ⟨c,hc,hok,hl,hrr⟩ := hr i i.isLt
    simp only [SignPartition.rootCell,LatticeSimple.Pattern.toSignPartition,mem_Icc] at hx
    rw [hc]
    have hl' : (c.spec.left:ℝ) ≤ (w.pat.node ((i:ℕ)+1):ℝ)-(w.pat.delta ((i:ℕ)+1):ℝ) := by exact_mod_cast hl
    have hr' : (w.pat.node ((i:ℕ)+1):ℝ)+(w.pat.delta ((i:ℕ)+1):ℝ) ≤ (c.spec.right:ℝ) := by exact_mod_cast hrr
    exact hbound c hok x ⟨by linarith [hx.1],by linarith [hx.2]⟩
  refine signPattern_bound w.pat a b total hp hab f hf (w.signAway ok a b hw f hsign)
    cap w.ep w.em hcap ?_ ?_ ?_ ?_ hscalar
  · intro i _; unfold Side.ep; split <;> simp
  · intro i _; unfold Side.em; split <;> simp
  · intro i x hx
    have h := (hroot i x hx).2
    unfold Side.ep
    revert h
    cases hc : w.roots[(i:ℕ)]? with
    | none => obtain ⟨c,hc',-⟩ := hr i i.isLt; rw [hc] at hc'; cases hc'
    | some c =>
      intro h
      rw [dec_eq_ratCast] at h
      have : (((c.upper:ℚ)/(S:ℚ):ℚ):ℝ) ≤ ((max ((c.upper:ℚ)/(S:ℚ)) 0 : ℚ):ℝ) := by exact_mod_cast le_max_left _ _
      linarith
  · intro i x hx
    have h := (hroot i x hx).1
    unfold Side.em
    revert h
    cases hc : w.roots[(i:ℕ)]? with
    | none => obtain ⟨c,hc',-⟩ := hr i i.isLt; rw [hc] at hc'; cases hc'
    | some c =>
      intro h
      rw [dec_eq_ratCast] at h
      have : ((-(c.lower:ℚ)/(S:ℚ):ℚ):ℝ) ≤ ((max (-(c.lower:ℚ)/(S:ℚ)) 0 : ℚ):ℝ) := by exact_mod_cast le_max_left _ _
      have he : ((-(c.lower:ℚ)/(S:ℚ):ℚ):ℝ)= -((((c.lower:ℚ)/(S:ℚ):ℚ):ℝ)) := by push_cast; ring
      linarith

/-- `∫₀^Y (W - θ)₊` from passed W cells, the pattern and the positive-gap caps. -/
theorem WSide.penalty (s : SourceF) (logs : List LogEntry) (r : SourceR) (z θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ2] (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (lk : WLink s logs r z θ Y σ1 σ2 d K) (w : Side) (hw : w.check (WCell.ok s logs) 0 s.Y=true)
    (hf : ContinuousOn (fun x : ℝ => W z (σ1+σ2) (x:ℂ)-θ) (Icc ((0:ℚ):ℝ) (s.Y:ℝ)))
    (cap : ℕ → ℚ)
    (hcap : ∀ i, i < w.pat.gaps → w.pat.positive i=true →
      (∫ x in (w.pat.node i:ℝ)..(w.pat.node (i+1):ℝ), W z (σ1+σ2) (x:ℂ)-θ) ≤ (cap i:ℝ))
    (total : ℚ) (hscalar : decide (w.pat.plusCap cap+w.pat.rootCap w.ep w.em ≤ total)=true) :
    (∫ x in ((0:ℚ):ℝ)..(s.Y:ℝ), pos (W z (σ1+σ2) (x:ℂ)-θ)) ≤ (total:ℝ) :=
  Side.penalty (WCell.ok s logs) 0 s.Y w hw _ hf
    (fun c hc x hx => c.bound s logs r z θ Y σ1 σ2 d K lk hc x hx)
    (fun c hc bb hb x hx => c.sign s logs r z θ Y σ1 σ2 d K lk hc bb hb x hx) cap hcap total hscalar

/-- `G̃(a) = a² log a/2 − a²/4` at a rational `a ≥ 0`. -/
def gtBoxF (lg : ℚ → Option FBox) (a : ℚ) : Option FBox :=
  if a=0 then some boxZero else
    (lg a).map fun la => boxSubF (boxMulF (boxOfQ (a^2/2)) la) (boxOfQ (a^2/4))

theorem gtBoxF_sound (lg : ℚ → Option FBox) (hlg : ∀ a b, lg a=some b → Contains b (Real.log (a:ℝ)))
    (a : ℚ) (b : FBox) (h : gtBoxF lg a=some b) : Contains b (Gtilde (a:ℝ)) := by
  unfold gtBoxF at h
  split_ifs at h with h0
  · cases h; subst h0; simpa [Gtilde] using boxZero_sound
  · cases hl : lg a with
    | none => rw [hl] at h; cases h
    | some la =>
      rw [hl] at h; simp only [Option.map_some,Option.some.injEq] at h; subst h
      have := boxSubF_sound _ _ _ _ (boxMulF_sound _ _ _ _ (boxOfQ_sound (a^2/2)) (hlg a la hl))
        (boxOfQ_sound (a^2/4))
      convert this using 1; unfold Gtilde; push_cast; ring

/-- A sum of boxed terms over `range n`. -/
def sumBoxF (t : ℕ → FBox) (n : ℕ) : FBox := (List.range n).foldl (fun acc j => boxAddF acc (t j)) boxZero

theorem sumBoxF_sound (t : ℕ → FBox) (v : ℕ → ℝ) (n : ℕ) (h : ∀ j < n, Contains (t j) (v j)) :
    Contains (sumBoxF t n) (∑ j ∈ Finset.range n, v j) := by
  induction n with
  | zero => simpa [sumBoxF] using boxZero_sound
  | succ n ih =>
    have ih' := ih (fun j hj => h j (by omega))
    unfold sumBoxF at ih' ⊢
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,Finset.sum_range_succ]
    exact boxAddF_sound _ _ _ _ ih' (h n (by omega))

/-- The second-segment multipole primitive at `dx = x − y₀`, from the moment boxes `MU`. -/
def mpPrimF (MU : List FBox) (m2 : FBox) (dx : ℚ) (ld : FBox) : FBox :=
  boxAddF (boxAddF (boxNegF (boxMulF m2 (boxSubF (boxMulF (boxOfQ dx) ld) (boxOfQ dx))))
    (boxMulF (MU.getD 0 boxZero) ld))
    (sumBoxF (fun j => boxMulF (MU.getD (j+1) boxZero) (boxOfQ (-((dx^(j+1))⁻¹)/((j:ℚ)+1)))) (MU.length-1))

theorem forall2_getD (MU : List FBox) (w : ℕ → ℝ) (h : List.Forall₂ Contains MU ((List.range MU.length).map w))
    (j : ℕ) (hj : j < MU.length) : Contains (MU.getD j boxZero) (w j) := by
  have hl := h.length_eq
  have := List.forall₂_iff_get.mp h
  have hj' : j < ((List.range MU.length).map w).length := by simp; exact hj
  have hg := this.2 j hj hj'
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using hg

theorem mpPrimF_sound (MU : List FBox) (m2 : FBox) (dx : ℚ) (ld : FBox) (hdx : 0 < dx)
    (σ2 : Measure ℂ) (y0 : ℝ) (hdxR : (dx:ℝ)=0+((dx:ℝ))) (M2 : ℝ) (hM2 : Contains m2 M2)
    (hld : Contains ld (Real.log (dx:ℝ))) (w : ℕ → ℝ)
    (hMU : List.Forall₂ Contains MU ((List.range MU.length).map w)) (hK : 0 < MU.length)
    (hw : ∀ k, w k=(moment σ2 (y0:ℂ) (k+1)).re/((k+1:ℕ):ℝ)) (hm2 : M2=σ2.real univ) (s : ℝ)
    (hs : s-y0=(dx:ℝ)) :
    Contains (mpPrimF MU m2 dx ld) (multipolePrimitive σ2 y0 s MU.length) := by
  have hdx0 : (0:ℝ) < (dx:ℝ) := by exact_mod_cast hdx
  have h1 := boxNegF_sound _ _ (boxMulF_sound _ _ _ _ hM2
    (boxSubF_sound _ _ _ _ (boxMulF_sound _ _ _ _ (boxOfQ_sound dx) hld) (boxOfQ_sound dx)))
  have h2 := boxMulF_sound _ _ _ _ (forall2_getD MU w hMU 0 hK) hld
  have h3 := sumBoxF_sound (fun j => boxMulF (MU.getD (j+1) boxZero) (boxOfQ (-((dx^(j+1))⁻¹)/((j:ℚ)+1))))
    (fun j => w (j+1)*(((-((dx^(j+1))⁻¹)/((j:ℚ)+1)):ℚ):ℝ)) (MU.length-1)
    (fun j hj => boxMulF_sound _ _ _ _ (forall2_getD MU w hMU (j+1) (by omega)) (boxOfQ_sound _))
  have h := boxAddF_sound _ _ _ _ (boxAddF_sound _ _ _ _ h1 h2) h3
  unfold mpPrimF
  convert h using 1
  unfold multipolePrimitive
  rw [if_pos hK,hs,hm2]
  have hsum : ∑ k ∈ Finset.Icc 2 MU.length,(moment σ2 (y0:ℂ) k).re*(dx:ℝ)^((1:ℤ)-k)/((k:ℝ)*(1-k))=
      ∑ j ∈ Finset.range (MU.length-1),w (j+1)*(((-((dx^(j+1))⁻¹)/((j:ℚ)+1)):ℚ):ℝ) := by
    have he : Finset.Icc 2 MU.length=Finset.Ico 2 (MU.length+1) := rfl
    rw [he,Finset.sum_Ico_eq_sum_range,show MU.length+1-2=MU.length-1 by omega]
    apply Finset.sum_congr rfl
    intro j _
    rw [hw (j+1)]
    have hz : ((1:ℤ)-((2+j:ℕ):ℤ))= -((j+1:ℕ):ℤ) := by push_cast; ring
    rw [hz,zpow_neg,zpow_natCast]
    have hj1 : ((j:ℝ)+1) ≠ 0 := by positivity
    have hj2 : ((j:ℝ)+2) ≠ 0 := by positivity
    have hd : (dx:ℝ)^(j+1) ≠ 0 := pow_ne_zero _ hdx0.ne'
    have hj0 : (0:ℝ) ≤ j := by positivity
    have hj3 : (1:ℝ)-(2+(j:ℝ)) ≠ 0 := by intro h; linarith
    have hj4 : (-1:ℝ)-(j:ℝ) ≠ 0 := by intro h; linarith
    push_cast
    field_simp
    ring
  rw [hsum,hw 0]
  push_cast
  ring

/-- The lattice primitive `P` of `W − θ` at a rational point `x ≥ 0` of `[0, Y]`. -/
def primBoxF (s : SourceF) (lg : ℚ → Option FBox) (qI : List FBox) (x : ℚ) : Option FBox :=
  (gtBoxF lg (x+1)).bind fun g1 => (gtBoxF lg (x+4)).bind fun g4 => (gtBoxF lg x).bind fun g0 =>
  (lg (x-s.y0)).bind fun ld =>
  some (boxSubF (boxSubF (boxAddF (boxAddF (boxSubF (boxSubF (boxScaleF 3 g1) g4) (boxScaleF 2 g0))
      (boxMulF (boxSubF (boxSubF boxOne (boxScaleF 2 s.U1c)) (boxOfQ s.theta)) (boxOfQ x)))
      (boxMulF s.L (boxOfQ (x^2/2))))
    (boxScaleF 2 (polyEvalF (boxOfQ x) qI))) (boxScaleF 2 (mpPrimF s.MU s.m2 (x-s.y0) ld)))

theorem polyEvalF_sound (xb : FBox) (x : ℝ) (hx : Contains xb x) :
    ∀ (p : List FBox) (vals : List ℝ), List.Forall₂ Contains p vals →
      ∀ (acc : FBox) (a : ℝ), Contains acc a →
        Contains (p.foldl (fun v c => boxAddF c (boxMulF xb v)) acc) (vals.foldl (fun t b => x*t+b) a)
  | [],[],_,acc,a,h => by simpa using h
  | c::cs,v::vs,h,acc,a,ha => by
    have hh := List.forall₂_cons.mp h
    simp only [List.foldl_cons]
    have := polyEvalF_sound xb x hx cs vs hh.2 _ _ (boxAddF_sound _ _ _ _ hh.1 (boxMulF_sound _ _ _ _ hx ha))
    convert this using 2; ring


theorem primBoxF_sound (s : SourceF) (logs : List LogEntry) (r : SourceR) (z θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ2] (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (lk : WLink s logs r z θ Y σ1 σ2 d K) (ids : List ℕ) (qI : List FBox) (qIv : List ℝ)
    (hqI : List.Forall₂ Contains qI qIv)
    (hqIe : ∀ x : ℝ, qIv.foldl (fun t b => x*t+b) 0=(ownUPoly d).integral.eval x)
    (hK0 : 0 < s.MU.length) (x : ℚ) (hx : 0 ≤ x) (b : FBox)
    (h : primBoxF s (fun a => lookupLogF logs a ids) qI x=some b) :
    Contains b (latticePrimitive z θ d K (x:ℝ)) := by
  have hlg : ∀ a c, (fun a => lookupLogF logs a ids) a=some c → Contains c (Real.log (a:ℝ)) :=
    fun a c hc => lookupLogF_sound logs lk.logs a ids c hc
  obtain ⟨-,hm2,hL,hU1c,-,-,-,-,hMU,-,-⟩ := lk.enc
  simp only [primBoxF,Option.bind_eq_some_iff,Option.some.injEq] at h
  obtain ⟨g1,hg1,g4,hg4,g0,hg0,ld,hld,rfl⟩ := h
  have G1 := gtBoxF_sound _ hlg _ _ hg1
  have G4 := gtBoxF_sound _ hlg _ _ hg4
  have G0 := gtBoxF_sound _ hlg _ _ hg0
  have LD := hlg _ _ hld
  have hy : (s.y0:ℝ) < 0 := by rw [lk.hy0]; exact d.y0_neg
  have hy' : s.y0 < 0 := by exact_mod_cast hy
  have hxR : (0:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have MP := mpPrimF_sound s.MU s.m2 (x-s.y0) ld (by linarith) σ2 d.y0 (by ring) r.M2 hm2 LD r.w hMU hK0
    lk.hw lk.hM2 (x:ℝ) (by push_cast; rw [lk.hy0])
  have LIN := boxMulF_sound _ _ _ _ (boxSubF_sound _ _ _ _ (boxSubF_sound _ _ _ _ boxOne_sound
    (boxScaleF_sound 2 _ _ hU1c)) (boxOfQ_sound s.theta)) (boxOfQ_sound x)
  have QUAD := boxMulF_sound _ _ _ _ hL (boxOfQ_sound (x^2/2))
  have POLY := polyEvalF_sound (boxOfQ x) (x:ℝ) (boxOfQ_sound x) qI qIv hqI boxZero 0 boxZero_sound
  have ALL := boxSubF_sound _ _ _ _ (boxSubF_sound _ _ _ _ (boxAddF_sound _ _ _ _ (boxAddF_sound _ _ _ _
    (boxSubF_sound _ _ _ _ (boxSubF_sound _ _ _ _ (boxScaleF_sound 3 _ _ G1) G4) (boxScaleF_sound 2 _ _ G0))
    LIN) QUAD) (boxScaleF_sound 2 _ _ POLY)) (boxScaleF_sound 2 _ _ MP)
  unfold polyEvalF
  convert ALL using 1
  unfold latticePrimitive
  rw [← lk.hK,hqIe,lk.hU1c,lk.hL,lk.hθ]
  push_cast
  ring

/-- The closed-form bound on the integral of `W − θ` over a gap `[p, q] ⊆ [0, Y]`. -/
theorem gapIntegral_le (s : SourceF) (logs : List LogEntry) (r : SourceR) (z θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ1] [IsFiniteMeasure σ2] (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (lk : WLink s logs r z θ Y σ1 σ2 d K) (ids : List ℕ) (qI : List FBox) (qIv : List ℝ)
    (hqI : List.Forall₂ Contains qI qIv)
    (hqIe : ∀ x : ℝ, qIv.foldl (fun t b => x*t+b) 0=(ownUPoly d).integral.eval x)
    (hK0 : 0 < s.MU.length) (p q : ℚ) (hp : 0 ≤ p) (hpq : p ≤ q) (hqY : q ≤ s.Y) (bp bq : FBox)
    (hbp : primBoxF s (fun a => lookupLogF logs a ids) qI p=some bp)
    (hbq : primBoxF s (fun a => lookupLogF logs a ids) qI q=some bq) :
    (∫ x in (p:ℝ)..(q:ℝ), W z (σ1+σ2) (x:ℂ)-θ) ≤ dec S bq.2-dec S bp.1+dec S s.globalW*((q:ℝ)-(p:ℝ)) := by
  have hP := primBoxF_sound s logs r z θ Y σ1 σ2 d K lk ids qI qIv hqI hqIe hK0 p hp bp hbp
  have hQ := primBoxF_sound s logs r z θ Y σ1 σ2 d K lk ids qI qIv hqI hqIe hK0 q (hp.trans hpq) bq hbq
  have hpR : (0:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hpqR : (p:ℝ) ≤ (q:ℝ) := by exact_mod_cast hpq
  have hqYR : (q:ℝ) ≤ Y := by rw [← lk.hYs]; exact_mod_cast hqY
  have hI := integral_W_closed z θ Y p q lk.hY ⟨hpR,hpqR,hqYR⟩ σ1 σ2 d K
    (mpErr (σ2.real univ) (d.supportRadius/(-d.y0)) K)
    (fun x hx => second_mp_err Y σ1 σ2 d K x (hpR.trans hx.1))
  have hg : 2*mpErr (σ2.real univ) (d.supportRadius/(-d.y0)) K*((q:ℝ)-(p:ℝ)) ≤
      dec S s.globalW*((q:ℝ)-(p:ℝ)) := mul_le_mul_of_nonneg_right lk.hglob (by linarith)
  have := (abs_le.mp hI).2
  linarith [hP.1,hQ.2]


/-- A stored Right cell: spec and claimed integer upper bound. -/
structure RCell where
  spec : TCSpec
  lower : ℤ
  upper : ℤ

def RCell.ok (s : SourceF) (logs : List LogEntry) (c : RCell) : Bool :=
  (c.spec.kind==.Right) && tcCheck s logs c.spec c.lower c.upper none

def RCell.iv (c : RCell) : QInterval := ⟨c.spec.left,c.spec.right⟩

/-- Its share of the penalty: `max(upper, 0)·width`. -/
def RCell.cap (c : RCell) : ℚ := max ((c.upper:ℚ)/(S:ℚ)) 0*(c.spec.right-c.spec.left)

/-- Right of the first segment, up to the cutoff `C`: a chain of passed Right cells bounds
`∫_Y^C (W − θ)₊` by the sum of the cells' caps. -/
theorem RSide.penalty (s : SourceF) (logs : List LogEntry) (r : SourceR) (z θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ2] (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (lk : WLink s logs r z θ Y σ1 σ2 d K) (hM1 : r.M1=d.c 0)
    (hfk : ∀ t : ℝ, hornerR t (r.fk.reverse++[0])=∑ k ∈ Finset.range d.N,d.c (k+1)*t^(k+1)/((k+1:ℕ):ℝ))
    (C : ℚ) (cs : List RCell) (hch : chainCheck s.Y C (cs.map RCell.iv)=true)
    (hok : ∀ c ∈ cs, c.ok s logs=true)
    (hf : Continuous (fun x : ℝ => pos (W z (σ1+σ2) (x:ℂ)-θ))) :
    (∫ x in (s.Y:ℝ)..(C:ℝ), pos (W z (σ1+σ2) (x:ℂ)-θ)) ≤ (((cs.map RCell.cap).sum:ℚ):ℝ) := by
  apply chainCheck_cells_integral_bound s.Y C cs RCell.iv hch _ hf RCell.cap
  intro c hc
  have h := hok c hc
  simp only [RCell.ok,Bool.and_eq_true,beq_iff_eq] at h
  have hlr : (c.spec.left:ℝ) ≤ c.spec.right := by
    have hg := tcCheck_geom s logs c.spec c.lower c.upper none h.2
    simp only [tcGeometryCheck,Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨h0,-⟩,-⟩,-⟩,-⟩,-⟩ := hg
    exact_mod_cast (of_decide_eq_true h0).2.1
  have hpt : ∀ x ∈ Icc (c.spec.left:ℝ) (c.spec.right:ℝ),
      pos (W z (σ1+σ2) (x:ℂ)-θ) ≤ ((max ((c.upper:ℚ)/(S:ℚ)) 0 : ℚ):ℝ) := by
    intro x hx
    have hu := rightCell_upper s logs c.spec c.lower c.upper none h.2 r lk.logs lk.enc h.1 z θ Y lk.hY σ1 σ2 d K
      lk.hL lk.hθ lk.hy0 lk.hYs hM1 lk.hM2 (hfk _) lk.hK lk.hw lk.hglob x hx
    rw [dec_eq_ratCast] at hu
    unfold pos
    apply max_le
    · exact hu.trans (by exact_mod_cast le_max_left _ _)
    · exact_mod_cast le_max_right _ _
  calc (∫ x in (c.iv.left:ℝ)..(c.iv.right:ℝ), pos (W z (σ1+σ2) (x:ℂ)-θ))
      ≤ ∫ x in (c.spec.left:ℝ)..(c.spec.right:ℝ), (((max ((c.upper:ℚ)/(S:ℚ)) 0 : ℚ)):ℝ) :=
        intervalIntegral.integral_mono_on hlr (hf.intervalIntegrable _ _)
          intervalIntegrable_const hpt
    _ = ((c.cap:ℚ):ℝ) := by
        rw [intervalIntegral.integral_const,smul_eq_mul]; unfold RCell.cap; push_cast; ring


/-- The identifications an atom cell needs, bundled once per (datum, ρ). -/
structure ALink (s : SourceF) (logs : List LogEntry) (r : SourceR) (z ρ θ Y : ℝ) (σ1 σ2 : Measure ℂ)
    [IsFiniteMeasure σ1] (y0 rr : ℝ) (K : ℕ) (f2 : ℝ → ℝ) : Prop where
  logs : LogsOK logs
  enc : SourceEnc s r
  hY : 0 ≤ Y
  hs1 : σ1 {s | s.im ≠ 0 ∨ s.re<0 ∨ Y<s.re}=0
  hy : y0<0
  hsep : rr < -y0
  hrr : -1-y0 ≤ rr ∧ 4+y0 ≤ rr
  hL : r.L=Real.log |z|
  hρθ : ((s.rho+s.theta:ℚ):ℝ)=ρ+θ
  hU1y0 : r.U1y0=U σ1 (y0:ℂ)
  hi1 : ∀ x ∈ Icc (1:ℝ) 4, Integrable (fun v => Real.log ‖(-(x:ℂ))-v‖) σ1
  hi2 : ∀ x ∈ Icc (1:ℝ) 4, Integrable (fun v => Real.log ‖(-(x:ℂ))-v‖) σ2
  hU2 : ∀ x ∈ Icc (1:ℝ) 4, U σ2 (-(x:ℂ))=r.U2c+f2 x
  hqA : ∀ x ∈ Icc (1:ℝ) 4, hornerR x r.qA=f2 x+∑ k ∈ Finset.range (K+1),
    inverseMoment σ1 y0 k*(-x-y0)^k/(k:ℝ)
  hglob : 2*mpErr (σ1.real univ) (rr/(-y0)) K ≤ dec S s.globalA

def ACell.ok (s : SourceF) (logs : List LogEntry) (c : WCell) : Bool :=
  (c.spec.kind==.Atom || c.spec.kind==.AtomLeft || c.spec.kind==.AtomRight) &&
  decide (c.spec.kind=.Atom ∨ c.spec.right-c.spec.left ≤ 1/3) &&
  tcCheck s logs c.spec c.lower c.upper c.pos

theorem ACell.bound (s : SourceF) (logs : List LogEntry) (r : SourceR) (z ρ θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ1] (y0 rr : ℝ) (K : ℕ) (f2 : ℝ → ℝ)
    (lk : ALink s logs r z ρ θ Y σ1 σ2 y0 rr K f2) (c : WCell) (hc : ACell.ok s logs c=true)
    (x : ℝ) (hx : (c.spec.left:ℝ) ≤ x ∧ x ≤ c.spec.right) :
    dec S c.lower ≤ A z ρ (σ1+σ2) x-θ ∧ A z ρ (σ1+σ2) x-θ ≤ dec S c.upper := by
  simp only [ACell.ok,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at hc
  obtain ⟨⟨hk,hw⟩,ht⟩ := hc
  have hk' : c.spec.kind=.Atom ∨ c.spec.kind=.AtomLeft ∨ c.spec.kind=.AtomRight := by
    rcases hk with (h|h)|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hw' : c.spec.kind ≠ .Atom → c.spec.right-c.spec.left ≤ 1/3 := fun h => hw.resolve_left h
  exact atomCell_bound s logs c.spec c.lower c.upper c.pos ht r lk.logs lk.enc hk' hw' z ρ θ Y lk.hY σ1 σ2
    lk.hs1 y0 rr lk.hy lk.hsep lk.hrr K f2 lk.hL lk.hρθ lk.hU1y0 lk.hi1 lk.hi2 lk.hU2 lk.hqA lk.hglob x hx

theorem ACell.sign (s : SourceF) (logs : List LogEntry) (r : SourceR) (z ρ θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ1] (y0 rr : ℝ) (K : ℕ) (f2 : ℝ → ℝ)
    (lk : ALink s logs r z ρ θ Y σ1 σ2 y0 rr K f2) (c : WCell) (hc : ACell.ok s logs c=true)
    (b : Bool) (hpos : c.pos=some b) (x : ℝ) (hx : (c.spec.left:ℝ) ≤ x ∧ x ≤ c.spec.right) :
    if b then 0 ≤ A z ρ (σ1+σ2) x-θ else A z ρ (σ1+σ2) x-θ ≤ 0 := by
  have hbd := ACell.bound s logs r z ρ θ Y σ1 σ2 y0 rr K f2 lk c hc x hx
  have hc' := hc
  simp only [ACell.ok,Bool.and_eq_true] at hc'
  have hsg := tcCheck_sign s logs c.spec c.lower c.upper c.pos hc'.2
  cases b
  · simp only [Bool.false_eq_true,if_false]
    exact hbd.2.trans (dec_nonpos_of _ (hsg.2 hpos))
  · simp only [if_true]
    exact (dec_nonneg_of _ (hsg.1 hpos)).trans hbd.1

/-- The atom part of the penalty, `∫₁⁴ (A − θ)₊`, from passed atom cells, the pattern and the caps. -/
theorem ASide.penalty (s : SourceF) (logs : List LogEntry) (r : SourceR) (z ρ θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ1] (y0 rr : ℝ) (K : ℕ) (f2 : ℝ → ℝ)
    (lk : ALink s logs r z ρ θ Y σ1 σ2 y0 rr K f2) (w : Side) (hw : w.check (ACell.ok s logs) 1 4=true)
    (hf : ContinuousOn (fun x : ℝ => A z ρ (σ1+σ2) x-θ) (Icc ((1:ℚ):ℝ) ((4:ℚ):ℝ)))
    (cap : ℕ → ℚ)
    (hcap : ∀ i, i < w.pat.gaps → w.pat.positive i=true →
      (∫ x in (w.pat.node i:ℝ)..(w.pat.node (i+1):ℝ), A z ρ (σ1+σ2) x-θ) ≤ (cap i:ℝ))
    (total : ℚ) (hscalar : decide (w.pat.plusCap cap+w.pat.rootCap w.ep w.em ≤ total)=true) :
    (∫ x in ((1:ℚ):ℝ)..((4:ℚ):ℝ), pos (A z ρ (σ1+σ2) x-θ)) ≤ (total:ℝ) :=
  Side.penalty (ACell.ok s logs) 1 4 w hw _ hf
    (fun c hc x hx => ACell.bound s logs r z ρ θ Y σ1 σ2 y0 rr K f2 lk c hc x hx)
    (fun c hc bb hb x hx => ACell.sign s logs r z ρ θ Y σ1 σ2 y0 rr K f2 lk c hc bb hb x hx)
    cap hcap total hscalar


/-- The atom primitive `2G̃(x) − 3G̃(x−1) + G̃(4−x) + (1−ρ−θ)x − L x²/2 − 2∫P` at a rational `x ∈ [1, 4]`. -/
theorem integral_C_add_eval (k : ℝ) (p : Polynomial ℝ) (x : ℝ) :
    (Polynomial.C k+p).integral.eval x=k*x+p.integral.eval x := by
  set G : Polynomial ℝ := Polynomial.C k*Polynomial.X+p.integral
  have hd : Polynomial.derivative ((Polynomial.C k+p).integral-G)=0 := by
    simp only [G,Polynomial.derivative_sub,Polynomial.derivative_add,Polynomial.derivative_integral,
      Polynomial.derivative_mul,Polynomial.derivative_C,Polynomial.derivative_X,zero_mul,mul_one,zero_add,sub_self]
  have hc := Polynomial.eq_C_of_derivative_eq_zero hd
  have h0 : ((Polynomial.C k+p).integral-G).eval 0=0 := by
    simp [G,Polynomial.integral_eval_zero]
  rw [hc,Polynomial.eval_C] at h0
  rw [h0,map_zero,sub_eq_zero] at hc
  rw [hc]; simp [G]

/-- The atom primitive `2G̃(x) − 3G̃(x−1) + G̃(4−x) + (1−ρ−θ)x − L x²/2 − 2((U₂c+U₁(y₀))x + ∫P_A)` at a
rational `x ∈ [1, 4]`; the stored list `qAI` is the antiderivative of the rational part `P_A`. -/
def atomPrimBoxF (s : SourceF) (lg : ℚ → Option FBox) (qAI : List FBox) (x : ℚ) : Option FBox :=
  (gtBoxF lg x).bind fun g0 => (gtBoxF lg (x-1)).bind fun g1 => (gtBoxF lg (4-x)).bind fun g4 =>
  some (boxSubF (boxSubF (boxAddF (boxAddF (boxSubF (boxScaleF 2 g0) (boxScaleF 3 g1)) g4)
      (boxMulF (boxSubF boxOne (boxOfQ (s.rho+s.theta))) (boxOfQ x)))
      (boxMulF s.L (boxOfQ (x^2/2))))
    (boxScaleF 2 (boxAddF (boxMulF (boxAddF s.U2c s.U1y0) (boxOfQ x)) (polyEvalF (boxOfQ x) qAI))))

theorem atomPrimBoxF_sound (s : SourceF) (logs : List LogEntry) (r : SourceR) (z ρ θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ1] (y0 rr : ℝ) (K : ℕ) (f2 : ℝ → ℝ)
    (lk : ALink s logs r z ρ θ Y σ1 σ2 y0 rr K f2) (ids : List ℕ) (qApoly : Polynomial ℝ)
    (qAI : List FBox) (qAIv : List ℝ) (hqAI : List.Forall₂ Contains qAI qAIv)
    (hqAIe : ∀ x : ℝ, qAIv.foldl (fun t b => x*t+b) 0=qApoly.integral.eval x)
    (x : ℚ) (b : FBox) (h : atomPrimBoxF s (fun a => lookupLogF logs a ids) qAI x=some b) :
    Contains b (atomPrimitive z ρ θ (Polynomial.C (r.U2c+r.U1y0)+qApoly) (x:ℝ)) := by
  have hlg : ∀ a c, (fun a => lookupLogF logs a ids) a=some c → Contains c (Real.log (a:ℝ)) :=
    fun a c hc => lookupLogF_sound logs lk.logs a ids c hc
  obtain ⟨-,-,hL,-,hU2c,hU1y0,-,-,-,-,-⟩ := lk.enc
  simp only [atomPrimBoxF,Option.bind_eq_some_iff,Option.some.injEq] at h
  obtain ⟨g0,hg0,g1,hg1,g4,hg4,rfl⟩ := h
  have G0 := gtBoxF_sound _ hlg _ _ hg0
  have G1 := gtBoxF_sound _ hlg _ _ hg1
  have G4 := gtBoxF_sound _ hlg _ _ hg4
  have LIN := boxMulF_sound _ _ _ _ (boxSubF_sound _ _ _ _ boxOne_sound (boxOfQ_sound (s.rho+s.theta)))
    (boxOfQ_sound x)
  have QUAD := boxMulF_sound _ _ _ _ hL (boxOfQ_sound (x^2/2))
  have CST := boxMulF_sound _ _ _ _ (boxAddF_sound _ _ _ _ hU2c hU1y0) (boxOfQ_sound x)
  have POLY := polyEvalF_sound (boxOfQ x) (x:ℝ) (boxOfQ_sound x) qAI qAIv hqAI boxZero 0 boxZero_sound
  have ALL := boxSubF_sound _ _ _ _ (boxSubF_sound _ _ _ _ (boxAddF_sound _ _ _ _ (boxAddF_sound _ _ _ _
    (boxSubF_sound _ _ _ _ (boxScaleF_sound 2 _ _ G0) (boxScaleF_sound 3 _ _ G1)) G4) LIN) QUAD)
    (boxScaleF_sound 2 _ _ (boxAddF_sound _ _ _ _ CST POLY))
  unfold polyEvalF
  convert ALL using 1
  unfold atomPrimitive
  have hρθ' : ((s.rho:ℚ):ℝ)+((s.theta:ℚ):ℝ)=ρ+θ := by rw [← lk.hρθ]; push_cast; ring
  rw [integral_C_add_eval,hqAIe,lk.hL]
  push_cast
  linear_combination (x:ℝ)*hρθ'

/-- The closed-form bound on the integral of `A − θ` over a gap `[p, q] ⊆ [1, 4]`. -/
theorem atomGapIntegral_le (s : SourceF) (logs : List LogEntry) (r : SourceR) (z ρ θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ1] (y0 rr : ℝ) (K : ℕ) (f2 : ℝ → ℝ)
    (lk : ALink s logs r z ρ θ Y σ1 σ2 y0 rr K f2) (dd : CatalanCore.Li2.Uniform.DualDatum)
    (hσ : dd.σ=σ1+σ2) (ids : List ℕ) (qApoly : Polynomial ℝ)
    (hqA' : ∀ x : ℝ, qApoly.eval x=hornerR x r.qA)
    (qAI : List FBox) (qAIv : List ℝ) (hqAI : List.Forall₂ Contains qAI qAIv)
    (hqAIe : ∀ x : ℝ, qAIv.foldl (fun t b => x*t+b) 0=qApoly.integral.eval x)
    (p q : ℚ) (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ 4) (bp bq : FBox)
    (hbp : atomPrimBoxF s (fun a => lookupLogF logs a ids) qAI p=some bp)
    (hbq : atomPrimBoxF s (fun a => lookupLogF logs a ids) qAI q=some bq) :
    (∫ x in (p:ℝ)..(q:ℝ), A z ρ (σ1+σ2) x-θ) ≤ dec S bq.2-dec S bp.1+dec S s.globalA*((q:ℝ)-(p:ℝ)) := by
  have hP := atomPrimBoxF_sound s logs r z ρ θ Y σ1 σ2 y0 rr K f2 lk ids qApoly qAI qAIv hqAI hqAIe p bp hbp
  have hQ := atomPrimBoxF_sound s logs r z ρ θ Y σ1 σ2 y0 rr K f2 lk ids qApoly qAI qAIv hqAI hqAIe q bq hbq
  have hpR : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hpqR : (p:ℝ) ≤ (q:ℝ) := by exact_mod_cast hpq
  have hqR : (q:ℝ) ≤ 4 := by exact_mod_cast hq
  have hmod := logPot_stieltjes_model σ1 y0 rr Y lk.hy (by linarith [lk.hrr.1,lk.hrr.2]) lk.hY lk.hsep lk.hs1 K
  have hR : ∀ x ∈ Icc (p:ℝ) (q:ℝ), |U dd.σ (-(x:ℂ))-(Polynomial.C (r.U2c+r.U1y0)+qApoly).eval x| ≤
      mpErr (σ1.real univ) (rr/(-y0)) K := by
    intro x hx
    have hx14 : x ∈ Icc (1:ℝ) 4 := ⟨hpR.trans hx.1,hx.2.trans hqR⟩
    rw [hσ,U_add_of_integrable σ1 σ2 _ (lk.hi1 x hx14) (lk.hi2 x hx14),lk.hU2 x hx14,
      Polynomial.eval_add,Polynomial.eval_C,hqA',lk.hqA x hx14,lk.hU1y0]
    have hb := hmod.2.2 (-x-y0) (abs_le.mpr ⟨by linarith [hx14.2,lk.hrr.2],by linarith [hx14.1,lk.hrr.1]⟩)
    rw [evalModel_stieltjesCoeffs] at hb
    beta_reduce at hb
    have he : (((y0+(-x-y0):ℝ)):ℂ)=-(x:ℂ) := by push_cast; ring
    rw [he] at hb
    convert hb using 2; ring
  have hI := integral_A_closed z ρ θ p q dd _ ⟨hpR,hpqR,hqR⟩ _ hR
  rw [hσ] at hI
  have hg : 2*mpErr (σ1.real univ) (rr/(-y0)) K*((q:ℝ)-(p:ℝ)) ≤ dec S s.globalA*((q:ℝ)-(p:ℝ)) :=
    mul_le_mul_of_nonneg_right lk.hglob (by linarith)
  have := (abs_le.mp hI).2
  linarith [hP.1,hQ.2]

end
end CatalanCore.Li2.DecayCert.Simple
