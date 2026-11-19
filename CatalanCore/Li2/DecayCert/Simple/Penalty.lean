module
public import CatalanCore.Li2.DecayCert.Simple.Bridge
public import CatalanCore.Li2.DecayCert.Lattice.Simple.Pattern
public import CatalanCore.Li2.DecayCert.Covers.LinePartition
/-! The `[0, Y]` part of the lattice penalty from passed TC cells. `WLink` bundles the source
identifications of a datum. A `WSide` is a sign pattern on `[0, Y]`, one chain of sign cells per gap away
from the roots and one root cell per root. `WSide.signAway` gives `W - θ` the pattern's sign away from the
roots, and `WSide.penalty` bounds `∫₀^Y (W - θ)₊` by the positive-gap integrals plus the root-cell error
(`signPattern_bound`). -/
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

/-- A stored W cell: its spec, its claimed integer range and its sign claim. -/
structure WCell where
  spec : TCSpec
  lower : ℤ
  upper : ℤ
  pos : Option Bool

def WCell.ok (s : SourceF) (logs : List LogEntry) (c : WCell) : Bool :=
  (c.spec.kind==.W) && tcCheck s logs c.spec c.lower c.upper c.pos

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
  simp only [WCell.ok,Bool.and_eq_true,beq_iff_eq] at hc
  exact wCell_bound s logs c.spec c.lower c.upper c.pos hc.2 r lk.logs lk.enc hc.1 z θ Y lk.hY σ1 σ2 d K
    lk.hL lk.hθ lk.hy0 lk.hYs lk.hM2 lk.hU1c lk.hq1 lk.hK lk.hw lk.hglob x hx

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

/-- The W side on `[0, Y]`: a sign pattern, one chain of sign cells per gap away from the roots, and
one root cell per root. -/
structure WSide where
  pat : Pattern
  away : List (List WCell)
  roots : List WCell

def WSide.check (s : SourceF) (logs : List LogEntry) (w : WSide) : Bool :=
  w.pat.check 0 s.Y && decide (w.away.length=w.pat.gaps ∧ w.roots.length=w.pat.gaps-1) &&
  (List.range w.pat.gaps).all (fun i => match w.away[i]? with
    | some cs => decide (w.pat.awayLo i < w.pat.awayHi i) && chainCheck (w.pat.awayLo i) (w.pat.awayHi i) (cs.map WCell.iv) &&
        cs.all (fun c => c.ok s logs && decide (c.pos=some (w.pat.positive i)))
    | none => false) &&
  (List.range (w.pat.gaps-1)).all (fun i => match w.roots[i]? with
    | some c => c.ok s logs && decide (c.spec.left ≤ w.pat.node (i+1)-w.pat.delta (i+1) ∧
        w.pat.node (i+1)+w.pat.delta (i+1) ≤ c.spec.right)
    | none => false)


theorem WSide.check_parts (s : SourceF) (logs : List LogEntry) (w : WSide) (hw : w.check s logs=true) :
    w.pat.check 0 s.Y=true ∧
    (∀ i, i < w.pat.gaps → ∃ cs, w.away[i]?=some cs ∧ w.pat.awayLo i < w.pat.awayHi i ∧
      chainCheck (w.pat.awayLo i) (w.pat.awayHi i) (cs.map WCell.iv)=true ∧
      ∀ c ∈ cs, c.ok s logs=true ∧ c.pos=some (w.pat.positive i)) ∧
    (∀ i, i < w.pat.gaps-1 → ∃ c, w.roots[i]?=some c ∧ c.ok s logs=true ∧
      c.spec.left ≤ w.pat.node (i+1)-w.pat.delta (i+1) ∧ w.pat.node (i+1)+w.pat.delta (i+1) ≤ c.spec.right) := by
  simp only [WSide.check,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hw
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

/-- Passed sign cells give `W - θ` its pattern's sign away from the root cells on `[0, Y]`. -/
theorem WSide.signAway (s : SourceF) (logs : List LogEntry) (r : SourceR) (z θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ2] (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (lk : WLink s logs r z θ Y σ1 σ2 d K) (w : WSide) (hw : w.check s logs=true) :
    (w.pat.toSignPartition 0 s.Y (w.check_parts s logs hw).1).signAway
      (fun x => W z (σ1+σ2) (x:ℂ)-θ) := by
  obtain ⟨hp,ha,-⟩ := w.check_parts s logs hw
  have hpp := w.pat.check_parts 0 s.Y hp
  intro i hi x hx hnot
  change i < w.pat.gaps at hi
  change x ∈ Icc (w.pat.node i:ℝ) (w.pat.node (i+1):ℝ) at hx
  change if w.pat.positive i then 0 ≤ W z (σ1+σ2) (x:ℂ)-θ else W z (σ1+σ2) (x:ℂ)-θ ≤ 0
  obtain ⟨cs,-,hlt,hch,hcs⟩ := ha i hi
  -- x lies in the away interval of gap i
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
  exact c.sign s logs r z θ Y σ1 σ2 d K lk (hcs c hc).1 _ (hcs c hc).2 x hxc


/-- Root-cell bounds `ep i ≥ sup (W - θ)` and `em i ≥ sup (θ - W)`, as rationals. -/
def WSide.ep (w : WSide) (i : ℕ) : ℚ := match w.roots[i]? with
  | some c => max ((c.upper:ℚ)/(S:ℚ)) 0 | none => 0
def WSide.em (w : WSide) (i : ℕ) : ℚ := match w.roots[i]? with
  | some c => max (-(c.lower:ℚ)/(S:ℚ)) 0 | none => 0

theorem dec_eq_ratCast (a : ℤ) : dec S a=(((a:ℚ)/(S:ℚ):ℚ):ℝ) := by
  unfold dec; push_cast; rfl

/-- The `[0, Y]` part of the lattice penalty: passed cells and a pattern bound `∫₀^Y (W - θ)₊` by the
pattern's positive-gap integrals plus the root-cell error. -/
theorem WSide.penalty (s : SourceF) (logs : List LogEntry) (r : SourceR) (z θ Y : ℝ)
    (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ2] (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (lk : WLink s logs r z θ Y σ1 σ2 d K) (w : WSide) (hw : w.check s logs=true)
    (hf : ContinuousOn (fun x : ℝ => W z (σ1+σ2) (x:ℂ)-θ) (Icc ((0:ℚ):ℝ) (s.Y:ℝ)))
    (cap : ℕ → ℚ)
    (hcap : ∀ i, i < w.pat.gaps → w.pat.positive i=true →
      (∫ x in (w.pat.node i:ℝ)..(w.pat.node (i+1):ℝ), W z (σ1+σ2) (x:ℂ)-θ) ≤ (cap i:ℝ))
    (total : ℚ) (hscalar : decide (w.pat.plusCap cap+w.pat.rootCap w.ep w.em ≤ total)=true) :
    (∫ x in ((0:ℚ):ℝ)..(s.Y:ℝ), pos (W z (σ1+σ2) (x:ℂ)-θ)) ≤ (total:ℝ) := by
  obtain ⟨hp,-,hr⟩ := w.check_parts s logs hw
  have hpp := w.pat.check_parts 0 s.Y hp
  have hab : (0:ℚ) ≤ s.Y := by
    have := hpp.2.1 0 w.pat.gaps hpp.1.1 le_rfl
    rw [hpp.1.2.1,hpp.1.2.2] at this; exact this.le
  have hroot : ∀ i : Fin (w.pat.gaps-1), ∀ x ∈ (w.pat.toSignPartition 0 s.Y hp).rootCell i,
      dec S (match w.roots[(i:ℕ)]? with | some c => c.lower | none => 0) ≤ W z (σ1+σ2) (x:ℂ)-θ ∧
      W z (σ1+σ2) (x:ℂ)-θ ≤ dec S (match w.roots[(i:ℕ)]? with | some c => c.upper | none => 0) := by
    intro i x hx
    obtain ⟨c,hc,hok,hl,hrr⟩ := hr i i.isLt
    simp only [SignPartition.rootCell,LatticeSimple.Pattern.toSignPartition,mem_Icc] at hx
    rw [hc]
    have hl' : (c.spec.left:ℝ) ≤ (w.pat.node ((i:ℕ)+1):ℝ)-(w.pat.delta ((i:ℕ)+1):ℝ) := by exact_mod_cast hl
    have hr' : (w.pat.node ((i:ℕ)+1):ℝ)+(w.pat.delta ((i:ℕ)+1):ℝ) ≤ (c.spec.right:ℝ) := by exact_mod_cast hrr
    exact c.bound s logs r z θ Y σ1 σ2 d K lk hok x ⟨by linarith [hx.1],by linarith [hx.2]⟩
  refine signPattern_bound w.pat 0 s.Y total hp hab _ hf (w.signAway s logs r z θ Y σ1 σ2 d K lk hw)
    cap w.ep w.em hcap ?_ ?_ ?_ ?_ hscalar
  · intro i _; unfold WSide.ep; split <;> simp
  · intro i _; unfold WSide.em; split <;> simp
  · intro i x hx
    have h := (hroot i x hx).2
    unfold WSide.ep
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
    unfold WSide.em
    revert h
    cases hc : w.roots[(i:ℕ)]? with
    | none => obtain ⟨c,hc',-⟩ := hr i i.isLt; rw [hc] at hc'; cases hc'
    | some c =>
      intro h
      rw [dec_eq_ratCast] at h
      have : ((-(c.lower:ℚ)/(S:ℚ):ℚ):ℝ) ≤ ((max (-(c.lower:ℚ)/(S:ℚ)) 0 : ℚ):ℝ) := by exact_mod_cast le_max_left _ _
      have he : ((-(c.lower:ℚ)/(S:ℚ):ℚ):ℝ)= -((((c.lower:ℚ)/(S:ℚ):ℚ):ℝ)) := by push_cast; ring
      linarith

end
end CatalanCore.Li2.DecayCert.Simple
