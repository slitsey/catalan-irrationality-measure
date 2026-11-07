module

public import CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
public import CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section
set_option Elab.async false

/-!
# C5 `MarkedPilot`: the negative marked row, profile and spatial tail

For the actual source `CapSourceData.capSource` and the sign `-1` (the cheap sign: the column
radii are `q <= 1/3` and the analytic tails are below `1e-39`):

* `pilotW : Profile` and `pilot_ok : Profile.OK pilotW capSource (sgOf Sign.neg)`. The signed
  densities are the exact rational differences of the anchor-1 and anchor-0 cells, merged by
  a generic sorted merge (`mergeA`, `evQ_mergeA`; no sortedness is needed for soundness) and
  turned into a chain of segments with their jump atoms (`chainQ`, `atoms_of_chain`).
* `pilot_hV`: the bounded-variation tail `dirV 2048 ... <= pilotM / 2^192` (`pilotM / 2^192` is
  0.0352730433, so `2/N Mx = 3.4446e-5`), through `dirV_le_of_packed` and `conv_guard`. Every
  Newton square root is checked in the kernel (`sqOK`).
* `logFx_spec`: a generic fixed-point logarithm of a positive rational with a rigorous error
  (`log w = 2 atanh ((w-1)/(w+1))`, an exact integer power loop), for the seeds of the coefficient
  streams.
* `pilot_majorant_enclosed`: `SourceMajorant capSource Sign.neg p dP tail` from the profile, the
  spatial tail and two numeric obligations (enclosures of the five coefficient streams, and the
  numeric bound of `streamTail`). These two are NOT proved here.

kcost: `pilot_checks` 11 s measured (about 8k Rat operations), `pilot_bin_checks` 55 s measured
(4096 grid roots, 8.5k pair roots, 1 Mbit product). No other `decide +kernel`.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.MarkedPilot

noncomputable section

open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

/-! ### Atoms with integer keys and rational weights -/

/-- An atom: key `a` (the point `a / 10^12`) and a rational weight. -/
abbrev Ev := ℤ × ℚ

def evQ (E : List Ev) (F : ℝ → ℝ) : ℝ :=
  (E.map fun e => ((e.2 : ℚ) : ℝ) * F ((e.1 : ℝ) / 10 ^ 12)).sum

@[simp] theorem evQ_nil (F : ℝ → ℝ) : evQ [] F = 0 := by simp [evQ]

@[simp] theorem evQ_cons (e : Ev) (E : List Ev) (F : ℝ → ℝ) :
    evQ (e :: E) F = ((e.2 : ℚ) : ℝ) * F ((e.1 : ℝ) / 10 ^ 12) + evQ E F := by simp [evQ]

theorem evQ_append (A B : List Ev) (F : ℝ → ℝ) : evQ (A ++ B) F = evQ A F + evQ B F := by
  simp [evQ]

def atomR (e : Ev) : ℝ × ℝ := ((e.1 : ℝ) / 10 ^ 12, ((e.2 : ℚ) : ℝ))

theorem evE_atomR (E : List Ev) (F : ℝ → ℝ) : evE (E.map atomR) F = evQ E F := by
  unfold evE evQ
  simp [List.map_map, Function.comp_def, atomR]

/-- Merge of two key-sorted atom lists, adding the weights at equal keys. Fuel only truncates. -/
def mergeA : ℕ → List Ev → List Ev → List Ev
  | 0, A, B => A ++ B
  | _ + 1, [], B => B
  | _ + 1, a :: A, [] => a :: A
  | f + 1, a :: A, b :: B =>
    if a.1 < b.1 then a :: mergeA f A (b :: B)
    else if b.1 < a.1 then b :: mergeA f (a :: A) B
    else (a.1, a.2 + b.2) :: mergeA f A B

theorem evQ_mergeA : ∀ (f : ℕ) (A B : List Ev) (F : ℝ → ℝ),
    evQ (mergeA f A B) F = evQ A F + evQ B F
  | 0, A, B, F => by simp [mergeA, evQ_append]
  | f + 1, [], B, F => by simp [mergeA]
  | f + 1, a :: A, [], F => by simp [mergeA]
  | f + 1, a :: A, b :: B, F => by
    rw [mergeA]
    split_ifs with h1 h2
    · simp only [evQ_cons, evQ_mergeA f A (b :: B) F]; ring
    · simp only [evQ_cons, evQ_mergeA f (a :: A) B F]; ring
    · have : a.1 = b.1 := by omega
      simp only [evQ_cons, evQ_mergeA f A B F, this]; push_cast; ring

def negEv (E : List Ev) : List Ev := E.map fun e => (e.1, -e.2)

theorem evQ_negEv (E : List Ev) (F : ℝ → ℝ) : evQ (negEv E) F = - evQ E F := by
  induction E with
  | nil => simp [negEv]
  | cons e E ih => simp only [negEv, List.map_cons, evQ_cons] at ih ⊢; push_cast; rw [ih]; ring

/-! ### Cell lists as atoms -/

/-- Density of the cell `t` of anchor mass `m` and total `T`, per unit of `y`. -/
def dens (m : ℚ) (T : ℤ) (t : Tr) : ℚ := m * t.2.2 / T * 10 ^ 12 / (t.2.1 - t.1)

def loEv (m : ℚ) (T : ℤ) (L : List Tr) : List Ev := L.map fun t => (t.1, dens m T t)
def hiEv (m : ℚ) (T : ℤ) (L : List Tr) : List Ev := L.map fun t => (t.2.1, - dens m T t)

theorem evC_cells (m : ℚ) (T : ℤ) (hm : 0 ≤ m) (hT : 0 < T) :
    ∀ (L : List Tr), (∀ t ∈ L, t.1 < t.2.1 ∧ 0 ≤ t.2.2) → ∀ F : ℝ → ℝ,
      evC (L.map (mkCell (m : ℝ) T)) F = -(evQ (loEv m T L) F + evQ (hiEv m T L) F)
  | [], _, F => by simp [evC, loEv, hiEv]
  | t :: L, hv, F => by
    have ih := evC_cells m T hm hT L (fun s hs => hv s (List.mem_cons_of_mem _ hs)) F
    have hvt := hv t List.mem_cons_self
    have hm' : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    obtain ⟨hlo, hhi, hw⟩ := mkCell_eq (m := (m : ℝ)) (T := T) hvt hT.le hm'
    have hba : (0 : ℝ) < (t.2.1 : ℝ) - t.1 := by
      have : (t.1 : ℝ) < t.2.1 := by exact_mod_cast hvt.1
      linarith
    have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    have e1 : evC ((t :: L).map (mkCell (m : ℝ) T)) F =
        (mkCell (m : ℝ) T t).w / ((mkCell (m : ℝ) T t).hi - (mkCell (m : ℝ) T t).lo) *
          (F (mkCell (m : ℝ) T t).hi - F (mkCell (m : ℝ) T t).lo) +
        evC (L.map (mkCell (m : ℝ) T)) F := by
      simp [evC]
    have e2 : loEv m T (t :: L) = (t.1, dens m T t) :: loEv m T L := rfl
    have e3 : hiEv m T (t :: L) = (t.2.1, - dens m T t) :: hiEv m T L := rfl
    rw [e1, ih, e2, e3, evQ_cons, evQ_cons, hlo, hhi, hw]
    have hd : ((dens m T t : ℚ) : ℝ) = (m : ℝ) * t.2.2 / T * 10 ^ 12 / ((t.2.1 : ℝ) - t.1) := by
      unfold dens; push_cast; ring
    simp only [Rat.cast_neg, hd]
    have h12 : ((t.2.1 : ℝ) / 10 ^ 12 - (t.1 : ℝ) / 10 ^ 12) = ((t.2.1 : ℝ) - t.1) / 10 ^ 12 := by ring
    rw [h12]
    field_simp
    ring

def cellEv (m : ℚ) (T : ℤ) (L : List Tr) : List Ev :=
  mergeA (2 * L.length) (loEv m T L) (hiEv m T L)

def diffEv (m1 : ℚ) (T1 : ℤ) (L1 : List Tr) (m0 : ℚ) (T0 : ℤ) (L0 : List Tr) : List Ev :=
  mergeA (4 * (L1.length + L0.length)) (cellEv m1 T1 L1) (negEv (cellEv m0 T0 L0))

theorem evC_diff {m1 m0 : ℚ} {T1 T0 : ℤ} {L1 L0 : List Tr} (h1 : 0 ≤ m1) (h0 : 0 ≤ m0)
    (hT1 : 0 < T1) (hT0 : 0 < T0) (hv1 : ∀ t ∈ L1, t.1 < t.2.1 ∧ 0 ≤ t.2.2)
    (hv0 : ∀ t ∈ L0, t.1 < t.2.1 ∧ 0 ≤ t.2.2) (F : ℝ → ℝ) :
    evC (L1.map (mkCell (m1 : ℝ) T1)) F - evC (L0.map (mkCell (m0 : ℝ) T0)) F =
      - evQ (diffEv m1 T1 L1 m0 T0 L0) F := by
  unfold diffEv cellEv
  rw [evQ_mergeA, evQ_negEv, evQ_mergeA, evQ_mergeA, evC_cells m1 T1 h1 hT1 L1 hv1,
    evC_cells m0 T0 h0 hT0 L0 hv0]
  ring

/-- The signed atoms of the anchor-1 minus anchor-0 rows and columns. -/
@[irreducible] def rowEv : List Ev := diffEv (49 / 50) (sumP row1) row1 1 (sumP row0) row0
@[irreducible] def colEv : List Ev := diffEv (49 / 50) (sumP col1) col1 1 (sumP col0) col0

theorem refRow_one : capSource.refRow 1 = row1.map (mkCell (((49 / 50 : ℚ)) : ℝ) (sumP row1)) := by
  show refRowF 1 = _
  unfold refRowF
  rw [if_neg (by decide)]
  norm_num

theorem refRow_zero : capSource.refRow 0 = row0.map (mkCell (((1 : ℚ)) : ℝ) (sumP row0)) := by
  show refRowF 0 = _
  unfold refRowF
  rw [if_pos rfl]
  norm_num

theorem refCol_one : capSource.refCol 1 = col1.map (mkCell (((49 / 50 : ℚ)) : ℝ) (sumP col1)) := by
  show refColF 1 = _
  unfold refColF
  rw [if_neg (by decide)]
  norm_num

theorem refCol_zero : capSource.refCol 0 = col0.map (mkCell (((1 : ℚ)) : ℝ) (sumP col0)) := by
  show refColF 0 = _
  unfold refColF
  rw [if_pos rfl]
  norm_num

theorem bind_row_Q (F : ℝ → ℝ) :
    evC (capSource.refRow 1) F - evC (capSource.refRow 0) F = - evQ rowEv F := by
  rw [refRow_one, refRow_zero]
  unfold rowEv
  exact evC_diff (by norm_num) (by norm_num) row1_tot row0_tot row1_ok row0_ok F

theorem bind_col_Q (F : ℝ → ℝ) :
    evC (capSource.refCol 1) F - evC (capSource.refCol 0) F = - evQ colEv F := by
  rw [refCol_one, refCol_zero]
  unfold colEv
  exact evC_diff (by norm_num) (by norm_num) col1_tot col0_tot col1_ok col0_ok F

/-! ### Sign split, mirror and chain -/

def posPart (E : List Ev) : List Ev := E.filter fun e => 0 ≤ e.1
def negPart (E : List Ev) : List Ev := E.filter fun e => e.1 < 0

theorem evQ_split (E : List Ev) (F : ℝ → ℝ) :
    evQ E F = evQ (posPart E) F + evQ (negPart E) F := by
  induction E with
  | nil => simp [posPart, negPart]
  | cons e E ih =>
    by_cases h : 0 ≤ e.1
    · have h2 : ¬ e.1 < 0 := not_lt.mpr h
      simp only [posPart, negPart, List.filter_cons, h, h2, decide_true, decide_false,
        if_true, Bool.false_eq_true, if_false, evQ_cons] at ih ⊢
      rw [ih]; ring
    · have h2 : e.1 < 0 := not_le.mp h
      simp only [posPart, negPart, List.filter_cons, h, h2, decide_true, decide_false,
        if_true, Bool.false_eq_true, if_false, evQ_cons] at ih ⊢
      rw [ih]; ring

theorem evQ_reverse (E : List Ev) (F : ℝ → ℝ) : evQ E.reverse F = evQ E F := by
  unfold evQ
  rw [List.map_reverse, List.sum_reverse]

/-- Reflection `y ↦ -y` of an atom list (reversed so keys stay ascending). -/
def mirror (E : List Ev) : List Ev := E.reverse.map fun e => (-e.1, -e.2)

theorem evQ_mirror (E : List Ev) (G : ℝ → ℝ) :
    evQ (mirror E) G = - evQ E (fun y => G (-y)) := by
  unfold mirror
  rw [← evQ_reverse E (fun y => G (-y))]
  generalize E.reverse = R
  induction R with
  | nil => simp
  | cons e R ih =>
    simp only [List.map_cons, evQ_cons] at ih ⊢
    rw [ih]
    push_cast
    rw [neg_div]
    ring

def chainQ : ℚ → List Ev → List (ℤ × ℤ × ℚ)
  | _, [] => []
  | _, [_] => []
  | acc, e :: e' :: rest => (e.1, e'.1, acc + e.2) :: chainQ (acc + e.2) (e' :: rest)

def segR (g : ℤ × ℤ × ℚ) : Seg :=
  ⟨(g.1 : ℝ) / 10 ^ 12, (g.2.1 : ℝ) / 10 ^ 12, ((g.2.2 : ℚ) : ℝ)⟩

def lastK : Ev → List Ev → ℤ
  | e, [] => e.1
  | _, e' :: r => lastK e' r

def sumW (E : List Ev) : ℚ := (E.map Prod.snd).sum

theorem evS_cons (g : Seg) (P : List Seg) (F : ℝ → ℝ) :
    evS (g :: P) F = g.rho * (F g.hi - F g.lo) + evS P F := by simp [evS]

theorem evS_chain : ∀ (E : List Ev) (e : Ev) (acc : ℚ) (F : ℝ → ℝ),
    evS ((chainQ acc (e :: E)).map segR) F =
      -(acc : ℝ) * F ((e.1 : ℝ) / 10 ^ 12) - evQ (e :: E) F +
        ((acc + sumW (e :: E) : ℚ) : ℝ) * F ((lastK e E : ℝ) / 10 ^ 12)
  | [], e, acc, F => by
    simp [chainQ, evS, lastK, sumW]
    ring
  | e' :: r, e, acc, F => by
    have ih := evS_chain r e' (acc + e.2) F
    have hc : chainQ acc (e :: e' :: r) = (e.1, e'.1, acc + e.2) :: chainQ (acc + e.2) (e' :: r) := rfl
    rw [hc, List.map_cons, evS_cons, ih]
    have hs : sumW (e :: e' :: r) = e.2 + sumW (e' :: r) := by simp [sumW]
    have hl : lastK e (e' :: r) = lastK e' r := rfl
    rw [hs, hl, evQ_cons (e) (e' :: r)]
    simp only [segR]
    push_cast
    ring

theorem atoms_of_chain (E : List Ev) (h : sumW E = 0) :
    Atoms ((chainQ 0 E).map segR) (E.map atomR) := by
  intro F
  rw [evE_atomR]
  cases E with
  | nil => simp [chainQ, evS, evQ]
  | cons e E =>
    rw [evS_chain E e 0 F, h]
    simp

def ascB : List Ev → Bool
  | e :: e' :: r => decide (e.1 < e'.1) && ascB (e' :: r)
  | _ => true

theorem chain_bounds {lo hi : ℤ} : ∀ (E : List Ev) (acc : ℚ), ascB E = true →
    (∀ e ∈ E, lo ≤ e.1 ∧ e.1 ≤ hi) → ∀ g ∈ chainQ acc E, g.1 < g.2.1 ∧ lo ≤ g.1 ∧ g.2.1 ≤ hi
  | [], _, _, _ => by simp [chainQ]
  | [_], _, _, _ => by simp [chainQ]
  | e :: e' :: r, acc, ha, hb => by
    intro g hg
    simp only [ascB, Bool.and_eq_true, decide_eq_true_eq] at ha
    rw [chainQ, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨ha.1, (hb e List.mem_cons_self).1, (hb e' (by simp)).2⟩
    · exact chain_bounds (e' :: r) (acc + e.2) ha.2
        (fun x hx => hb x (List.mem_cons_of_mem _ hx)) g hg

theorem evQ_congr {E : List Ev} {G G' : ℝ → ℝ} (h : ∀ y, G y = G' y) : evQ E G = evQ E G' := by
  have : G = G' := funext h
  rw [this]

theorem evQ_fun_neg (E : List Ev) (F : ℝ → ℝ) : evQ E (fun y => - F y) = - evQ E F := by
  induction E with
  | nil => simp
  | cons e E ih => simp only [evQ_cons] at ih ⊢; rw [ih]; ring

theorem physX_ge_inv {Y : ℝ} (hY : 2 ≤ Y) : 1 / Y ≤ YCell.physX Y := by
  unfold YCell.physX
  rw [if_pos (by linarith)]
  have h0 : 0 ≤ √(Y ^ 2 - 4) := Real.sqrt_nonneg _
  have h1 : √(Y ^ 2 - 4) ≤ Y := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-! ### The profile of the negative row -/

@[irreducible] def EsQ : List Ev := mirror (negPart rowEv)
@[irreducible] def EoQ : List Ev := posPart rowEv
@[irreducible] def EcQ : List Ev := mirror colEv

/-- The concrete profile for `capSource`, sign `-1`. The radii are constants, valid for
`y ≤ 11.01` (opposite direct), all `y ≥ 2` (opposite reflection) and `c ≤ 0` (column). -/
def pilotW : Profile where
  Ps := (chainQ 0 EsQ).map segR
  Po := (chainQ 0 EoQ).map segR
  Pc := (chainQ 0 EcQ).map segR
  Es := EsQ.map atomR
  Eo := EoQ.map atomR
  Ec := EcQ.map atomR
  qD := fun _ => 14 / 25
  qO := fun _ => 1 / 5
  qC := fun _ => 1 / 3

def pilotChecks : Bool :=
  decide (sumW EsQ = 0) && decide (sumW EoQ = 0) && decide (sumW EcQ = 0) &&
  ascB EsQ && ascB EoQ && ascB EcQ &&
  EsQ.all (fun e => decide (2000000000000 ≤ e.1 ∧ e.1 ≤ 11010000000000)) &&
  EoQ.all (fun e => decide (2000000000000 ≤ e.1 ∧ e.1 ≤ 11010000000000)) &&
  EcQ.all (fun e => decide (-999999999999 ≤ e.1 ∧ e.1 ≤ 0))

-- kcost: 4 merges of about 700 + 1400 atoms (Int compare, one ℚ add per tie), 1410 densities
-- (6 ℚ ops each), sumW over 3 lists of about 300-630 ℚ: about 60k kernel ops, estimated 4 s
theorem pilot_checks : pilotChecks = true := by decide +kernel

theorem seg_bounds {lo hi : ℤ} (E : List Ev) (ha : ascB E = true)
    (hb : ∀ e ∈ E, lo ≤ e.1 ∧ e.1 ≤ hi) :
    ∀ g ∈ (chainQ 0 E).map segR,
      (lo : ℝ) / 10 ^ 12 ≤ g.lo ∧ g.lo < g.hi ∧ g.hi ≤ (hi : ℝ) / 10 ^ 12 := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
  obtain ⟨h1, h2, h3⟩ := chain_bounds E 0 ha hb g0 hg0
  have h1' : (g0.1 : ℝ) < g0.2.1 := by exact_mod_cast h1
  have h2' : (lo : ℝ) ≤ g0.1 := by exact_mod_cast h2
  have h3' : (g0.2.1 : ℝ) ≤ hi := by exact_mod_cast h3
  simp only [segR]
  refine ⟨?_, ?_, ?_⟩ <;> gcongr

theorem pilot_ok : Profile.OK pilotW capSource (sgOf Sign.neg) := by
  have hc := pilot_checks
  simp only [pilotChecks, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsEs, hsEo⟩, hsEc⟩, ha1⟩, ha2⟩, ha3⟩, hb1⟩, hb2⟩, hb3⟩ := hc
  have hneg : sgOf Sign.neg = -1 := rfl
  have a1 : Atoms pilotW.Ps pilotW.Es := atoms_of_chain EsQ hsEs
  have a2 : Atoms pilotW.Po pilotW.Eo := atoms_of_chain EoQ hsEo
  have a3 : Atoms pilotW.Pc pilotW.Ec := atoms_of_chain EcQ hsEc
  refine ⟨a1, a2, a3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F
    rw [bind_row_Q F, hneg]
    have e1 : evS pilotW.Ps (fun y => -1 * F (-1 * y)) = - evQ EsQ (fun y => -1 * F (-1 * y)) := by
      have := a1 (fun y => -1 * F (-1 * y))
      rwa [show pilotW.Es = EsQ.map atomR from rfl, evE_atomR] at this
    have e2 : evS pilotW.Po (fun y => - -1 * F (- -1 * y)) = - evQ EoQ (fun y => - -1 * F (- -1 * y)) := by
      have := a2 (fun y => - -1 * F (- -1 * y))
      rwa [show pilotW.Eo = EoQ.map atomR from rfl, evE_atomR] at this
    have h1 : evQ EsQ (fun y => -1 * F (-1 * y)) = evQ (negPart rowEv) F := by
      unfold EsQ
      rw [evQ_mirror]
      have : evQ (negPart rowEv) (fun y => -1 * F (-1 * -y)) = - evQ (negPart rowEv) F := by
        rw [← evQ_fun_neg]; exact evQ_congr fun y => by simp
      rw [this]; ring
    have h2 : evQ EoQ (fun y => - -1 * F (- -1 * y)) = evQ (posPart rowEv) F := by
      unfold EoQ
      exact evQ_congr fun y => by simp
    rw [e1, e2, h1, h2, evQ_split rowEv F]
    ring
  · intro F
    rw [bind_col_Q F, hneg]
    have e1 : evS pilotW.Pc (fun y => -1 * F (-1 * y)) = - evQ EcQ (fun y => -1 * F (-1 * y)) := by
      have := a3 (fun y => -1 * F (-1 * y))
      rwa [show pilotW.Ec = EcQ.map atomR from rfl, evE_atomR] at this
    have h1 : evQ EcQ (fun y => -1 * F (-1 * y)) = evQ colEv F := by
      unfold EcQ
      rw [evQ_mirror]
      have : evQ colEv (fun y => -1 * F (-1 * -y)) = - evQ colEv F := by
        rw [← evQ_fun_neg]; exact evQ_congr fun y => by simp
      rw [this]; ring
    rw [e1, h1]
  · intro g hg
    have h := seg_bounds EsQ ha1 hb1 g hg
    refine ⟨?_, h.2.1⟩
    have := h.1; norm_num at this; linarith
  · intro g hg
    have h := seg_bounds EoQ ha2 hb2 g hg
    refine ⟨?_, h.2.1⟩
    have := h.1; norm_num at this; linarith
  · intro g hg
    have h := seg_bounds EcQ ha3 hb3 g hg
    have h1 := h.1; have h3 := h.2.2
    norm_num at h1 h3
    refine ⟨by linarith, h.2.1.le, by linarith⟩
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    have := (hb1 e0 he0).1
    have h' : ((2000000000000 : ℤ) : ℝ) ≤ e0.1 := by exact_mod_cast this
    simp only [atomR]
    rw [le_div_iff₀ (by positivity)]
    norm_num at h' ⊢
    linarith
  · intro g hg
    have h := seg_bounds EoQ ha2 hb2 g hg
    have h1 := h.1; have h3 := h.2.2
    norm_num at h1 h3
    have hp := physX_ge_inv (show (2:ℝ) ≤ g.hi by linarith [h.2.1])
    have hq : 1 / (1101 / 100 : ℝ) ≤ 1 / g.hi := one_div_le_one_div_of_le (by linarith [h.2.1]) h3
    show 0 < (14 / 25 : ℝ) ∧ (14 / 25 : ℝ) < 1 ∧
      (1 + (14 / 25 : ℝ) ^ 2) / (2 * (14 / 25)) ≤ 1 + 2 * YCell.physX g.hi
    refine ⟨by norm_num, by norm_num, ?_⟩
    norm_num at hq ⊢
    rw [one_div] at hp
    linarith
  · intro g hg
    have h := seg_bounds EoQ ha2 hb2 g hg
    have h1 := h.1
    norm_num at h1
    have hm := physX_mem (show (2:ℝ) ≤ g.lo by linarith)
    show 0 < (1 / 5 : ℝ) ∧ (1 / 5 : ℝ) < 1 ∧
      (1 + (1 / 5 : ℝ) ^ 2) / (2 * (1 / 5)) ≤ 1 + 2 / YCell.physX g.lo
    refine ⟨by norm_num, by norm_num, ?_⟩
    have : (2 : ℝ) ≤ 2 / YCell.physX g.lo := by
      rw [le_div_iff₀ hm.1]; linarith [hm.2]
    norm_num
    linarith
  · intro g hg
    have h := seg_bounds EcQ ha3 hb3 g hg
    have h3 := h.2.2
    norm_num at h3
    show 0 < (1 / 3 : ℝ) ∧ (1 / 3 : ℝ) < 1 ∧
      (1 + (1 / 3 : ℝ) ^ 2) / (2 * (1 / 3)) ≤ 1 + dC g.hi
    refine ⟨by norm_num, by norm_num, ?_⟩
    have : (7 / 5 : ℝ) ≤ dC g.hi := by
      unfold dC
      apply Real.le_sqrt_of_sq_le
      linarith
    norm_num
    linarith

/-! ### Integer square roots: Newton in the kernel, correctness checked -/

def isqrtIter (n : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => isqrtIter n k ((x + n / x) / 2)

/-- Newton from above; its result is never trusted, `sqOK` checks the bracket. -/
def isqrtN (n : ℕ) : ℕ :=
  let r := isqrtIter n 12 (2 ^ (n.log2 / 2 + 1))
  if r * r ≤ n then r else r - 1

def sqOK (n : ℕ) : Bool :=
  decide (isqrtN n * isqrtN n ≤ n ∧ n < (isqrtN n + 1) * (isqrtN n + 1))

theorem sqOK_spec {n : ℕ} (h : sqOK n = true) :
    isqrtN n * isqrtN n ≤ n ∧ n < (isqrtN n + 1) * (isqrtN n + 1) := by
  simpa [sqOK] using h

/-! ### The function `b` and its enclosures -/

theorem bb_sq {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) :
    bb s ^ 2 = (1 + s) ^ 2 * (1 - s) ^ 3 / s ^ 3 := by
  have hq : 0 ≤ (1 - s) / s := div_nonneg (by linarith) h0.le
  unfold bb
  rw [mul_pow, mul_pow, Real.sq_sqrt hq]
  field_simp

theorem bb_nonneg {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) : 0 ≤ bb s := by
  have hq : 0 ≤ (1 - s) / s := div_nonneg (by linarith) h0.le
  unfold bb
  positivity

theorem poly_anti {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (1 + t) ^ 2 * (1 - t) ^ 3 ≤ (1 + s) ^ 2 * (1 - s) ^ 3 := by
  have e : ∀ x : ℝ, (1 + x) ^ 2 * (1 - x) ^ 3 = (1 - x ^ 2) ^ 2 * (1 - x) := fun x => by ring
  rw [e, e]
  have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith
  have h1 : 1 - t ^ 2 ≤ 1 - s ^ 2 := by nlinarith
  exact mul_le_mul (pow_le_pow_left₀ h0 h1 2) (by linarith) (by linarith) (by positivity)

theorem bb_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1) : bb t ≤ bb s := by
  have ht0 : 0 < t := lt_of_lt_of_le hs hst
  have h := poly_anti hs.le hst ht
  have hu : bb t ^ 2 ≤ bb s ^ 2 := by
    rw [bb_sq ht0 ht, bb_sq hs (hst.trans ht)]
    have h3 : s ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ hs.le hst 3
    have h4 : 0 ≤ (1 + t) ^ 2 * (1 - t) ^ 3 := by
      have : 0 ≤ 1 - t := by linarith
      positivity
    calc (1 + t) ^ 2 * (1 - t) ^ 3 / t ^ 3 ≤ (1 + t) ^ 2 * (1 - t) ^ 3 / s ^ 3 :=
          div_le_div_of_nonneg_left h4 (by positivity) h3
      _ ≤ _ := div_le_div_of_nonneg_right h (by positivity)
  exact (pow_le_pow_iff_left₀ (bb_nonneg ht0 ht) (bb_nonneg hs (hst.trans ht)) two_ne_zero).1 hu

def bbN (P Q k : ℕ) : ℕ := (Q + P) ^ 2 * (Q - P) ^ 3 * 4 ^ k / (Q ^ 2 * P ^ 3)

theorem bb_enc {P Q k : ℕ} (hP : 0 < P) (hPQ : P ≤ Q) (hs : sqOK (bbN P Q k) = true) :
    (isqrtN (bbN P Q k) : ℝ) / 2 ^ k ≤ bb ((P : ℝ) / Q) ∧
      bb ((P : ℝ) / Q) ≤ ((isqrtN (bbN P Q k) : ℝ) + 1) / 2 ^ k := by
  obtain ⟨h1, h2⟩ := sqOK_spec hs
  have hQ : 0 < Q := lt_of_lt_of_le hP hPQ
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hs0 : 0 < (P : ℝ) / Q := div_pos hPr hQr
  have hs1 : (P : ℝ) / Q ≤ 1 := by rw [div_le_one hQr]; exact_mod_cast hPQ
  have hsq := bb_sq hs0 hs1
  have hb0 := bb_nonneg hs0 hs1
  set n := bbN P Q k with hn
  set r := isqrtN n
  set N : ℕ := (Q + P) ^ 2 * (Q - P) ^ 3 * 4 ^ k with hN
  set D : ℕ := Q ^ 2 * P ^ 3 with hD
  have hDp : 0 < D := by positivity
  have hDr : (0 : ℝ) < D := by exact_mod_cast hDp
  have hnN : (n : ℝ) ≤ (N : ℝ) / D := by
    rw [le_div_iff₀ hDr]; exact_mod_cast Nat.div_mul_le_self N D
  have hNn : (N : ℝ) / D < n + 1 := by
    rw [div_lt_iff₀ hDr]
    have : N < (n + 1) * D := (Nat.div_lt_iff_lt_mul hDp).1 (Nat.lt_succ_self n)
    exact_mod_cast this
  have hu : (N : ℝ) / D = bb ((P : ℝ) / Q) ^ 2 * (2 ^ k) ^ 2 := by
    rw [hsq, hN, hD]
    push_cast [Nat.cast_sub hPQ]
    rw [show ((2 : ℝ) ^ k) ^ 2 = 4 ^ k by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    field_simp
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have h1' : (r : ℝ) ^ 2 ≤ (bb ((P : ℝ) / Q) * 2 ^ k) ^ 2 := by
    have : (r : ℝ) * r ≤ n := by exact_mod_cast h1
    rw [mul_pow, ← hu]; nlinarith
  have h2' : (bb ((P : ℝ) / Q) * 2 ^ k) ^ 2 ≤ ((r : ℝ) + 1) ^ 2 := by
    have : (n : ℝ) + 1 ≤ (r + 1) * (r + 1) := by exact_mod_cast h2
    rw [mul_pow, ← hu]; nlinarith
  have hbk : 0 ≤ bb ((P : ℝ) / Q) * 2 ^ k := by positivity
  constructor
  · rw [div_le_iff₀ hk]
    exact (pow_le_pow_iff_left₀ (by positivity) hbk two_ne_zero).1 h1'
  · rw [le_div_iff₀ hk]
    exact (pow_le_pow_iff_left₀ hbk (by positivity) two_ne_zero).1 h2'

theorem physX_core {A M t r c : ℝ} (hA : 0 < A) (ht : 0 < t) (hr : 0 ≤ r) (hM0 : 0 ≤ M)
    (hc : 0 < c) (h1 : r * r ≤ M * t ^ 2) (h2 : M * t ^ 2 + 1 ≤ (r + 1) * (r + 1)) :
    2 * c * t / (A * t + r + 1) ≤ 2 * c / (A + √M) ∧ 2 * c / (A + √M) ≤ 2 * c * t / (A * t + r) := by
  have hr1 : r / t ≤ √M := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have hr2 : √M ≤ (r + 1) / t := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    nlinarith
  have hs0 : 0 ≤ √M := Real.sqrt_nonneg _
  constructor
  · have hd : A + √M ≤ (A * t + r + 1) / t := by
      have : (A * t + r + 1) / t = A + (r + 1) / t := by field_simp; ring
      rw [this]; linarith
    have e : 2 * c * t / (A * t + r + 1) = 2 * c / ((A * t + r + 1) / t) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hd
  · have hd : (A * t + r) / t ≤ A + √M := by
      have : (A * t + r) / t = A + r / t := by field_simp
      rw [this]; linarith
    have e : 2 * c * t / (A * t + r) = 2 * c / ((A * t + r) / t) := by
      field_simp
    rw [e]
    have hpos : 0 < (A * t + r) / t := by
      have : 0 < A * t := by positivity
      positivity
    exact div_le_div_of_nonneg_left (by positivity) hpos hd

theorem physX_enc {A t r : ℕ} (hA : 2000000000000 ≤ A) (ht : 0 < t)
    (h1 : r * r ≤ (A ^ 2 - 4 * 10 ^ 24) * t ^ 2) (h2 : (A ^ 2 - 4 * 10 ^ 24) * t ^ 2 < (r + 1) * (r + 1)) :
    (2 * 10 ^ 12 * t : ℝ) / (A * t + r + 1) ≤ YCell.physX (A / 10 ^ 12) ∧
      YCell.physX (A / 10 ^ 12) ≤ (2 * 10 ^ 12 * t : ℝ) / (A * t + r) := by
  have hA' : (2000000000000 : ℝ) ≤ A := by exact_mod_cast hA
  have hM : 4 * 10 ^ 24 ≤ A ^ 2 :=
    calc 4 * 10 ^ 24 = (2000000000000) ^ 2 := by norm_num
      _ ≤ A ^ 2 := Nat.pow_le_pow_left hA 2
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = A ^ 2 - 4 * 10 ^ 24 := ⟨_, rfl⟩
  rw [← hMdef] at h1 h2
  have hMr : (M : ℝ) = (A : ℝ) ^ 2 - 4 * 10 ^ 24 := by
    rw [hMdef, Nat.cast_sub hM]; push_cast; ring
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hy : (2 : ℝ) ≤ A / 10 ^ 12 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have hsq : √(((A : ℝ) / 10 ^ 12) ^ 2 - 4) = √(M : ℝ) / 10 ^ 12 := by
    rw [show (((A : ℝ) / 10 ^ 12) ^ 2 - 4) = (M : ℝ) / (10 ^ 12) ^ 2 by rw [hMr]; field_simp,
      Real.sqrt_div hM0, Real.sqrt_sq (by norm_num)]
  have hx : YCell.physX (A / 10 ^ 12) = 2 * 10 ^ 12 / (A + √(M : ℝ)) := by
    unfold YCell.physX
    rw [if_pos (by linarith), hsq]
    field_simp
  rw [hx]
  have h1' : (r : ℝ) * r ≤ M * (t : ℝ) ^ 2 := by exact_mod_cast h1
  have h2' : (M : ℝ) * (t : ℝ) ^ 2 + 1 ≤ (r + 1) * (r + 1) := by exact_mod_cast h2
  exact physX_core (A := (A : ℝ)) (M := (M : ℝ)) (t := (t : ℝ)) (r := (r : ℝ)) (c := 10 ^ 12)
    (by linarith) (by exact_mod_cast ht) (Nat.cast_nonneg r) hM0 (by norm_num) h1' h2'

/-! ### Bin pairs: the upper bin masses as a list of `(bin, value)` pairs -/

/-- Parameters of the bin guard: bins `B`, `b` scale `2^kb`, source-root scale `2^kP`, density scale `2^h`. -/
structure BinPar where
  B : ℕ
  kb : ℕ
  kP : ℕ
  h : ℕ

/-- `(P, Q)` with `P/Q ≤ physX (A / 10^12)`. -/
def pxLo (kP A : ℕ) : ℕ × ℕ :=
  (2 * 10 ^ 12 * 2 ^ kP, A * 2 ^ kP + isqrtN ((A ^ 2 - 4 * 10 ^ 24) * (2 ^ kP) ^ 2) + 1)

/-- `(P, Q)` with `physX (A / 10^12) ≤ P/Q`. -/
def pxHi (kP A : ℕ) : ℕ × ℕ :=
  (2 * 10 ^ 12 * 2 ^ kP, A * 2 ^ kP + isqrtN ((A ^ 2 - 4 * 10 ^ 24) * (2 ^ kP) ^ 2))

def pxOK (kP A : ℕ) : Bool := sqOK ((A ^ 2 - 4 * 10 ^ 24) * (2 ^ kP) ^ 2)

theorem pxLo_le {kP A : ℕ} (hA : 2000000000000 ≤ A) (hk : pxOK kP A = true) :
    ((pxLo kP A).1 : ℝ) / (pxLo kP A).2 ≤ YCell.physX (A / 10 ^ 12) := by
  obtain ⟨h1, h2⟩ := sqOK_spec hk
  have := (physX_enc (t := 2 ^ kP) hA (by positivity) h1 h2).1
  refine le_of_eq_of_le ?_ this
  unfold pxLo; push_cast; norm_num

theorem le_pxHi {kP A : ℕ} (hA : 2000000000000 ≤ A) (hk : pxOK kP A = true) :
    YCell.physX (A / 10 ^ 12) ≤ ((pxHi kP A).1 : ℝ) / (pxHi kP A).2 := by
  obtain ⟨h1, h2⟩ := sqOK_spec hk
  have := (physX_enc (t := 2 ^ kP) hA (by positivity) h1 h2).2
  refine le_trans this (le_of_eq ?_)
  unfold pxHi; push_cast; norm_num

/-- Upper / lower bounds `UB/2^kb ≥ bb (P/Q) ≥ LB/2^kb`. -/
def bbUp (kb P Q : ℕ) : ℕ := isqrtN (bbN P Q kb) + 1
def bbLo (kb P Q : ℕ) : ℕ := isqrtN (bbN P Q kb)

/-- Data of one segment `(lo key, hi key, rho)`. -/
structure SegEnc where
  a : ℕ × ℕ
  b : ℕ × ℕ
  jl : ℕ
  jh : ℕ
  rh : ℕ

/-- `⌈|ρ| 2^h⌉`. -/
def rhoHat (h : ℕ) (r : ℚ) : ℕ := (r.num.natAbs * 2 ^ h + r.den - 1) / r.den

def segEnc (p : BinPar) (g : ℤ × ℤ × ℚ) : SegEnc :=
  let a := pxLo p.kP g.2.1.toNat
  let b := pxHi p.kP g.1.toNat
  ⟨a, b, a.1 * p.B / a.2, min (b.1 * p.B / b.2) (p.B - 1), rhoHat p.h g.2.2⟩

def binPair (p : BinPar) (e : SegEnc) (j : ℕ) : ℕ × ℕ :=
  (j, e.rh * ((if j = e.jl then bbUp p.kb e.a.1 e.a.2 else bbUp p.kb j p.B) -
    (if j = e.jh then bbLo p.kb e.b.1 e.b.2 else bbLo p.kb (j + 1) p.B)))

def segPairs (p : BinPar) (g : ℤ × ℤ × ℚ) : List (ℕ × ℕ) :=
  let e := segEnc p g
  (List.range' e.jl (e.jh + 1 - e.jl)).map (binPair p e)

/-- An atom contributes `|W| * bbUp` on every bin its source point can lie in. -/
def atomPairs (p : BinPar) (a : Ev) : List (ℕ × ℕ) :=
  let lo := pxLo p.kP a.1.toNat
  let hi := pxHi p.kP a.1.toNat
  let jl := min (lo.1 * p.B / lo.2) (p.B - 1)
  let jh := min (hi.1 * p.B / hi.2) (p.B - 1)
  (List.range' jl (jh + 1 - jl)).map fun j => (j, rhoHat p.h a.2 * bbUp p.kb lo.1 lo.2)

/-- Value of the pairs with key `j`. -/
def pv (L : List (ℕ × ℕ)) (j : ℕ) : ℕ := (L.map fun q => if q.1 = j then q.2 else 0).sum

theorem pv_nil (j : ℕ) : pv [] j = 0 := rfl
theorem pv_cons (q : ℕ × ℕ) (L : List (ℕ × ℕ)) (j : ℕ) :
    pv (q :: L) j = (if q.1 = j then q.2 else 0) + pv L j := by simp [pv]
theorem pv_append (L M : List (ℕ × ℕ)) (j : ℕ) : pv (L ++ M) j = pv L j + pv M j := by
  simp [pv]

/-- Regrouping a list of pairs by key. -/
theorem sum_pairs {B : ℕ} : ∀ (L : List (ℕ × ℕ)), (∀ q ∈ L, q.1 < B) → ∀ f : ℕ → ℕ,
    (L.map fun q => q.2 * f q.1).sum = ∑ j ∈ Finset.range B, pv L j * f j
  | [], _, f => by simp [pv_nil]
  | q :: L, hk, f => by
    have ih := sum_pairs L (fun x hx => hk x (List.mem_cons_of_mem _ hx)) f
    simp only [List.map_cons, List.sum_cons, ih, pv_cons, add_mul, Finset.sum_add_distrib]
    congr 1
    have hq := hk q List.mem_cons_self
    rw [Finset.sum_eq_single q.1]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]; simp
    · intro h; exact absurd (Finset.mem_range.2 hq) h

/-! ### Small facts -/

theorem cast_toNat {z : ℤ} (h : 0 ≤ z) : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg h

theorem rhoHat_spec (h : ℕ) (r : ℚ) : |((r : ℚ) : ℝ)| ≤ (rhoHat h r : ℝ) / 2 ^ h := by
  have hd : 0 < r.den := r.den_pos
  have hdr : (0 : ℝ) < r.den := by exact_mod_cast hd
  have h2 : (0 : ℝ) < 2 ^ h := by positivity
  have hle : r.num.natAbs * 2 ^ h ≤ rhoHat h r * r.den := by
    unfold rhoHat
    obtain ⟨x, hx⟩ : ∃ x, x = r.num.natAbs * 2 ^ h := ⟨_, rfl⟩
    rw [← hx]
    have := Nat.lt_mul_div_succ (x + r.den - 1) hd
    rw [mul_add, mul_one, Nat.mul_comm r.den] at this
    omega
  have hr : |((r : ℚ) : ℝ)| = (r.num.natAbs : ℝ) / r.den := by
    rw [Rat.cast_def, abs_div, abs_of_pos hdr]
    congr 1
    simp [Nat.cast_natAbs]
  rw [hr, div_le_div_iff₀ hdr h2]
  have : ((r.num.natAbs * 2 ^ h : ℕ) : ℝ) ≤ ((rhoHat h r * r.den : ℕ) : ℝ) := by exact_mod_cast hle
  push_cast at this
  nlinarith

theorem pv_range'_map (f : ℕ → ℕ × ℕ) (hf : ∀ i, (f i).1 = i) (j : ℕ) :
    ∀ (n s : ℕ), pv ((List.range' s n).map f) j = if s ≤ j ∧ j < s + n then (f j).2 else 0
  | 0, s => by simp [pv_nil]
  | n + 1, s => by
    rw [List.range'_succ, List.map_cons, pv_cons, pv_range'_map f hf j n (s + 1), hf]
    by_cases h : s = j
    · subst h
      simp
    · rw [if_neg h, zero_add]
      by_cases h2 : s + 1 ≤ j ∧ j < s + 1 + n
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem tsub_cast (a b : ℕ) : ((a - b : ℕ) : ℝ) = max 0 ((a : ℝ) - b) := by
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h]
    have h1 : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [max_eq_left (by linarith)]
    simp
  · rw [Nat.cast_sub h]
    have h1 : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [max_eq_right (by linarith)]

theorem term_bound {X Y UA LB : ℝ} (hUA : X ≤ UA) (hLB : LB ≤ Y) :
    max 0 (X - Y) ≤ max 0 (UA - LB) := max_le_max le_rfl (by linarith)

theorem term_zero {sl sh ej ej1 : ℝ} (hsl : 0 < sl) (hmin : 0 < min sh ej1)
    (hle : min sh ej1 ≤ max sl ej) (hmax1 : max sl ej ≤ 1) :
    max 0 (bb (max sl ej) - bb (min sh ej1)) = 0 := by
  have h := bb_anti hmin hle hmax1
  exact max_eq_left (by linarith)

/-! ### One segment -/

def segOK (p : BinPar) (g : ℤ × ℤ × ℚ) : Bool :=
  pxOK p.kP g.1.toNat && pxOK p.kP g.2.1.toNat &&
  sqOK (bbN (segEnc p g).a.1 (segEnc p g).a.2 p.kb) &&
  sqOK (bbN (segEnc p g).b.1 (segEnc p g).b.2 p.kb) &&
  decide (1 ≤ (segEnc p g).jl ∧ (segEnc p g).jl ≤ (segEnc p g).jh ∧ (segEnc p g).jh < p.B)

def gridOK (p : BinPar) : Bool := (List.range' 1 p.B).all fun j => sqOK (bbN j p.B p.kb)

theorem gridOK_spec {p : BinPar} (h : gridOK p = true) :
    ∀ j, 1 ≤ j → j ≤ p.B → sqOK (bbN j p.B p.kb) = true := by
  intro j hj1 hj2
  unfold gridOK at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.2 ⟨hj1, by omega⟩)

theorem pxLo_pq {kP A : ℕ} (hA : 2000000000000 ≤ A) :
    0 < (pxLo kP A).1 ∧ (pxLo kP A).1 ≤ (pxLo kP A).2 := by
  unfold pxLo
  refine ⟨by positivity, ?_⟩
  have : 2 * 10 ^ 12 * 2 ^ kP ≤ A * 2 ^ kP := Nat.mul_le_mul_right _ (by omega)
  simp only
  omega

theorem pxHi_pq {kP A : ℕ} (hA : 2000000000000 ≤ A) :
    0 < (pxHi kP A).1 ∧ (pxHi kP A).1 ≤ (pxHi kP A).2 := by
  unfold pxHi
  refine ⟨by positivity, ?_⟩
  have : 2 * 10 ^ 12 * 2 ^ kP ≤ A * 2 ^ kP := Nat.mul_le_mul_right _ (by omega)
  simp only
  omega

theorem segEnc_jh (p : BinPar) (g : ℤ × ℤ × ℚ) :
    (segEnc p g).jh = min ((segEnc p g).b.1 * p.B / (segEnc p g).b.2) (p.B - 1) := rfl

theorem min_eq_of_lt {x B jh j : ℕ} (h : jh = min x (B - 1)) (hj : j < B) (hjh : jh < j) :
    jh = x := by omega

theorem seg_term (p : BinPar) (hB : 1 ≤ p.B) (g : ℤ × ℤ × ℚ) (hg1 : 2000000000000 ≤ g.1)
    (hg2 : g.1 < g.2.1) (hOK : segOK p g = true)
    (hgrid : ∀ j, 1 ≤ j → j ≤ p.B → sqOK (bbN j p.B p.kb) = true) (j : ℕ) (hj : j < p.B) :
    |((g.2.2 : ℚ) : ℝ)| *
        max 0 (bb (max (YCell.physX ((g.2.1 : ℝ) / 10 ^ 12)) ((j : ℝ) / p.B)) -
          bb (min (YCell.physX ((g.1 : ℝ) / 10 ^ 12)) (((j : ℝ) + 1) / p.B))) ≤
      (pv (segPairs p g) j : ℝ) / 2 ^ (p.kb + p.h) := by
  have hBr : (0 : ℝ) < p.B := by exact_mod_cast hB
  unfold segOK at hOK
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOK
  obtain ⟨⟨⟨⟨hk1, hk2⟩, hs1⟩, hs2⟩, hjl1, hjl2, hjh⟩ := hOK
  set e := segEnc p g with he
  have hAlo : 2000000000000 ≤ g.1.toNat := by omega
  have hAhi : 2000000000000 ≤ g.2.1.toNat := by omega
  have hc1 : ((g.1.toNat : ℕ) : ℝ) = (g.1 : ℝ) := cast_toNat (by omega)
  have hc2 : ((g.2.1.toNat : ℕ) : ℝ) = (g.2.1 : ℝ) := cast_toNat (by omega)
  have hpl := pxLo_le hAhi hk2
  have hph := le_pxHi hAlo hk1
  rw [hc2] at hpl
  rw [hc1] at hph
  have hae : e.a = pxLo p.kP g.2.1.toNat := rfl
  have hbe : e.b = pxHi p.kP g.1.toNat := rfl
  obtain ⟨ha0, ha1⟩ := pxLo_pq (kP := p.kP) hAhi
  obtain ⟨hb0, hb1⟩ := pxHi_pq (kP := p.kP) hAlo
  rw [← hae] at ha0 ha1 hpl
  rw [← hbe] at hb0 hb1 hph
  have haR : (0 : ℝ) < (e.a.1 : ℝ) / e.a.2 := by
    have : (0 : ℝ) < e.a.1 := by exact_mod_cast ha0
    have h2 : (0 : ℝ) < e.a.2 := by exact_mod_cast lt_of_lt_of_le ha0 ha1
    positivity
  have hbR : (0 : ℝ) < (e.b.1 : ℝ) / e.b.2 := by
    have : (0 : ℝ) < e.b.1 := by exact_mod_cast hb0
    have h2 : (0 : ℝ) < e.b.2 := by exact_mod_cast lt_of_lt_of_le hb0 hb1
    positivity
  have haR1 : (e.a.1 : ℝ) / e.a.2 ≤ 1 := by
    rw [div_le_one (by exact_mod_cast lt_of_lt_of_le ha0 ha1)]; exact_mod_cast ha1
  have hbR1 : (e.b.1 : ℝ) / e.b.2 ≤ 1 := by
    rw [div_le_one (by exact_mod_cast lt_of_lt_of_le hb0 hb1)]; exact_mod_cast hb1
  have hlo2 : (2 : ℝ) ≤ (g.1 : ℝ) / 10 ^ 12 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : (2000000000000 : ℤ) ≤ g.1) |>.trans' (by norm_num)
  have hhi2 : (2 : ℝ) ≤ (g.2.1 : ℝ) / 10 ^ 12 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : (2000000000000 : ℤ) ≤ g.2.1) |>.trans' (by norm_num)
  obtain ⟨hsl0, hsl1⟩ := physX_mem hhi2
  obtain ⟨hsh0, hsh1⟩ := physX_mem hlo2
  set sl := YCell.physX ((g.2.1 : ℝ) / 10 ^ 12) with hsl
  set sh := YCell.physX ((g.1 : ℝ) / 10 ^ 12) with hsh
  have hej0 : 0 ≤ (j : ℝ) / p.B := by positivity
  have hej1 : (j : ℝ) / p.B ≤ 1 := by
    rw [div_le_one hBr]; exact_mod_cast hj.le
  have hej1p : 0 < ((j : ℝ) + 1) / p.B := by positivity
  have hej11 : ((j : ℝ) + 1) / p.B ≤ 1 := by
    rw [div_le_one hBr]; exact_mod_cast hj
  have hrho := rhoHat_spec p.h g.2.2
  have hrho0 : 0 ≤ (rhoHat p.h g.2.2 : ℝ) / 2 ^ p.h := by positivity
  have hmax1 : max sl ((j : ℝ) / p.B) ≤ 1 := max_le hsl1 hej1
  have hmin0 : 0 < min sh (((j : ℝ) + 1) / p.B) := lt_min hsh0 hej1p
  have hRHS0 : (0 : ℝ) ≤ (pv (segPairs p g) j : ℝ) / 2 ^ (p.kb + p.h) := by positivity
  -- index facts
  have hjlR : (e.jl : ℝ) / p.B ≤ (e.a.1 : ℝ) / e.a.2 := by
    rw [div_le_iff₀ hBr]
    have h1 : (e.jl : ℝ) ≤ ((e.a.1 * p.B : ℕ) : ℝ) / e.a.2 := Nat.cast_div_le
    push_cast at h1
    have h2 : (0 : ℝ) < e.a.2 := by exact_mod_cast lt_of_lt_of_le ha0 ha1
    calc (e.jl : ℝ) ≤ (e.a.1 : ℝ) * p.B / e.a.2 := h1
      _ = (e.a.1 : ℝ) / e.a.2 * p.B := by ring
  rcases lt_or_ge j e.jl with hjl | hjl
  · -- below the segment
    have hle : min sh (((j : ℝ) + 1) / p.B) ≤ max sl ((j : ℝ) / p.B) := by
      have h1 : ((j : ℝ) + 1) / p.B ≤ (e.jl : ℝ) / p.B := by
        apply div_le_div_of_nonneg_right _ hBr.le
        exact_mod_cast hjl
      calc min sh (((j : ℝ) + 1) / p.B) ≤ ((j : ℝ) + 1) / p.B := min_le_right _ _
        _ ≤ (e.jl : ℝ) / p.B := h1
        _ ≤ (e.a.1 : ℝ) / e.a.2 := hjlR
        _ ≤ sl := hpl
        _ ≤ _ := le_max_left _ _
    rw [term_zero hsl0 hmin0 hle hmax1, mul_zero]
    exact hRHS0
  rcases lt_or_ge e.jh j with hjh' | hjh'
  · -- above the segment
    have hjhX : e.jh = e.b.1 * p.B / e.b.2 :=
      min_eq_of_lt (segEnc_jh p g) hj hjh'

    have hb2 : 0 < e.b.2 := lt_of_lt_of_le hb0 hb1
    have hlt : e.b.1 * p.B < e.b.2 * (e.jh + 1) := by
      rw [hjhX]; exact Nat.lt_mul_div_succ _ hb2
    have hbj : (e.b.1 : ℝ) / e.b.2 < (j : ℝ) / p.B := by
      rw [div_lt_div_iff₀ (by exact_mod_cast hb2) hBr]
      have h1 : ((e.b.1 * p.B : ℕ) : ℝ) < ((e.b.2 * (e.jh + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
      have h2 : ((e.jh : ℝ) + 1) ≤ j := by exact_mod_cast hjh'
      push_cast at h1
      have h3 : (0 : ℝ) < e.b.2 := by exact_mod_cast hb2
      nlinarith
    have hle : min sh (((j : ℝ) + 1) / p.B) ≤ max sl ((j : ℝ) / p.B) := by
      calc min sh (((j : ℝ) + 1) / p.B) ≤ sh := min_le_left _ _
        _ ≤ (e.b.1 : ℝ) / e.b.2 := hph
        _ ≤ (j : ℝ) / p.B := hbj.le
        _ ≤ _ := le_max_right _ _
    rw [term_zero hsl0 hmin0 hle hmax1, mul_zero]
    exact hRHS0
  -- the segment meets the bin
  have hjj : e.jl ≤ j ∧ j < e.jl + (e.jh + 1 - e.jl) := ⟨hjl, by omega⟩
  have hpv : pv (segPairs p g) j = (binPair p e j).2 := by
    unfold segPairs
    rw [pv_range'_map (binPair p e) (fun i => rfl) j _ _, if_pos hjj]
  have hj1 : 1 ≤ j := by omega
  -- upper bound for the first argument
  have hX : bb (max sl ((j : ℝ) / p.B)) ≤
      ((if j = e.jl then bbUp p.kb e.a.1 e.a.2 else bbUp p.kb j p.B : ℕ) : ℝ) / 2 ^ p.kb := by
    by_cases hje : j = e.jl
    · rw [if_pos hje]
      have h1 := (bb_enc (k := p.kb) ha0 ha1 hs1).2
      have h2 : bb (max sl ((j : ℝ) / p.B)) ≤ bb sl := bb_anti hsl0 (le_max_left _ _) hmax1
      have h3 : bb sl ≤ bb ((e.a.1 : ℝ) / e.a.2) := bb_anti haR hpl hsl1
      unfold bbUp
      push_cast
      linarith
    · rw [if_neg hje]
      have hjB := hgrid j hj1 hj.le
      have hjj0 : 0 < j := hj1
      have h1 := (bb_enc (k := p.kb) hjj0 hj.le hjB).2
      have h2 : bb (max sl ((j : ℝ) / p.B)) ≤ bb ((j : ℝ) / p.B) := by
        have hp : 0 < (j : ℝ) / p.B := by
          have : (0 : ℝ) < j := by exact_mod_cast hjj0
          positivity
        exact bb_anti hp (le_max_right _ _) hmax1
      unfold bbUp
      push_cast
      linarith
  have hY : ((if j = e.jh then bbLo p.kb e.b.1 e.b.2 else bbLo p.kb (j + 1) p.B : ℕ) : ℝ) / 2 ^ p.kb ≤
      bb (min sh (((j : ℝ) + 1) / p.B)) := by
    by_cases hje : j = e.jh
    · rw [if_pos hje]
      have h1 := (bb_enc (k := p.kb) hb0 hb1 hs2).1
      have h2 : bb ((e.b.1 : ℝ) / e.b.2) ≤ bb sh := bb_anti hsh0 hph hbR1
      have h3 : bb sh ≤ bb (min sh (((j : ℝ) + 1) / p.B)) := bb_anti hmin0 (min_le_left _ _) hsh1
      unfold bbLo
      push_cast
      linarith
    · rw [if_neg hje]
      have hjB := hgrid (j + 1) (by omega) (by omega)
      have h1 := (bb_enc (k := p.kb) (P := j + 1) (by omega) (by omega) hjB).1
      have h2 : bb (((j : ℝ) + 1) / p.B) ≤ bb (min sh (((j : ℝ) + 1) / p.B)) :=
        bb_anti hmin0 (min_le_right _ _) hej11
      unfold bbLo
      push_cast at h1 ⊢
      linarith
  set UA : ℕ := if j = e.jl then bbUp p.kb e.a.1 e.a.2 else bbUp p.kb j p.B with hUA
  set LB : ℕ := if j = e.jh then bbLo p.kb e.b.1 e.b.2 else bbLo p.kb (j + 1) p.B with hLB
  have hbp : (binPair p e j).2 = e.rh * (UA - LB) := rfl
  have hk2 : (0 : ℝ) < 2 ^ p.kb := by positivity
  have hM := term_bound hX hY
  have hmax : max 0 ((UA : ℝ) / 2 ^ p.kb - (LB : ℝ) / 2 ^ p.kb) = ((UA - LB : ℕ) : ℝ) / 2 ^ p.kb := by
    rw [tsub_cast, ← sub_div]
    rcases le_total (UA : ℝ) LB with h | h
    · rw [max_eq_left (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith [h]) , max_eq_left (by linarith)]
      simp
    · rw [max_eq_right (by apply div_nonneg <;> linarith), max_eq_right (by linarith)]
  rw [hmax] at hM
  have hM0 : 0 ≤ max 0 (bb (max sl ((j : ℝ) / p.B)) - bb (min sh (((j : ℝ) + 1) / p.B))) := le_max_left _ _
  calc |((g.2.2 : ℚ) : ℝ)| * max 0 (bb (max sl ((j : ℝ) / p.B)) - bb (min sh (((j : ℝ) + 1) / p.B)))
      ≤ ((rhoHat p.h g.2.2 : ℝ) / 2 ^ p.h) * (((UA - LB : ℕ) : ℝ) / 2 ^ p.kb) :=
        mul_le_mul hrho hM hM0 hrho0
    _ = (pv (segPairs p g) j : ℝ) / 2 ^ (p.kb + p.h) := by
        rw [hpv, hbp, pow_add]
        push_cast [Nat.cast_mul]
        field_simp
        have hrh : e.rh = rhoHat p.h g.2.2 := rfl
        rw [hrh]; ring

/-! ### One atom -/

def atomOK (p : BinPar) (a : Ev) : Bool :=
  pxOK p.kP a.1.toNat &&
  sqOK (bbN (pxLo p.kP a.1.toNat).1 (pxLo p.kP a.1.toNat).2 p.kb) &&
  decide (a.1 ≥ 2000000000000)

theorem floor_pq (P Q B : ℕ) : ⌊((P : ℝ) / Q) * B⌋₊ = P * B / Q := by
  have : ((P : ℝ) / Q) * B = ((P * B : ℕ) : ℝ) / Q := by push_cast; ring
  rw [this, Nat.floor_div_eq_div]

theorem atom_term (p : BinPar) (hB : 1 ≤ p.B) (a : Ev) (hOK : atomOK p a = true) (j : ℕ) :
    (if bidx p.B (YCell.physX ((a.1 : ℝ) / 10 ^ 12)) = j then
        |((a.2 : ℚ) : ℝ)| * bb (YCell.physX ((a.1 : ℝ) / 10 ^ 12)) else 0) ≤
      (pv (atomPairs p a) j : ℝ) / 2 ^ (p.kb + p.h) := by
  have hBr : (0 : ℝ) < p.B := by exact_mod_cast hB
  unfold atomOK at hOK
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOK
  obtain ⟨⟨hk, hs⟩, hA⟩ := hOK
  have hA' : 2000000000000 ≤ a.1.toNat := by omega
  have hc : ((a.1.toNat : ℕ) : ℝ) = (a.1 : ℝ) := cast_toNat (by omega)
  have hpl := pxLo_le hA' hk
  have hph := le_pxHi hA' hk
  rw [hc] at hpl hph
  obtain ⟨ha0, ha1⟩ := pxLo_pq (kP := p.kP) hA'
  obtain ⟨hb0, hb1⟩ := pxHi_pq (kP := p.kP) hA'
  have hy2 : (2 : ℝ) ≤ (a.1 : ℝ) / 10 ^ 12 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (2000000000000 : ℝ) ≤ a.1 := by exact_mod_cast hA
    linarith
  obtain ⟨hs0, hs1⟩ := physX_mem hy2
  set s := YCell.physX ((a.1 : ℝ) / 10 ^ 12) with hsdef
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = pxLo p.kP a.1.toNat := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi, hi = pxHi p.kP a.1.toNat := ⟨_, rfl⟩
  rw [← hlo] at hpl ha0 ha1 hs
  rw [← hhi] at hph hb0 hb1
  have haR : (0 : ℝ) < (lo.1 : ℝ) / lo.2 := by
    have : (0 : ℝ) < lo.1 := by exact_mod_cast ha0
    have h2 : (0 : ℝ) < lo.2 := by exact_mod_cast lt_of_lt_of_le ha0 ha1
    positivity
  by_cases hb : bidx p.B s = j
  · rw [if_pos hb]
    -- the bin lies in [jl, jh]
    have hfl : ⌊s * p.B⌋₊ ≥ lo.1 * p.B / lo.2 := by
      rw [← floor_pq]
      exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hpl hBr.le)
    have hfh : ⌊s * p.B⌋₊ ≤ hi.1 * p.B / hi.2 := by
      rw [← floor_pq]
      exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hph hBr.le)
    have hbj : j = min ⌊s * p.B⌋₊ (p.B - 1) := hb.symm
    have hjl : min (lo.1 * p.B / lo.2) (p.B - 1) ≤ j := by omega
    have hjh : j ≤ min (hi.1 * p.B / hi.2) (p.B - 1) := by omega
    have hpv : pv (atomPairs p a) j = rhoHat p.h a.2 * bbUp p.kb lo.1 lo.2 := by
      unfold atomPairs
      rw [← hlo, ← hhi]
      rw [pv_range'_map (fun j => (j, rhoHat p.h a.2 * bbUp p.kb lo.1 lo.2)) (fun i => rfl) j _ _,
        if_pos ⟨hjl, by omega⟩]
    rw [hpv]
    have h1 := (bb_enc (k := p.kb) ha0 ha1 hs).2
    have h2 : bb s ≤ bb ((lo.1 : ℝ) / lo.2) := bb_anti haR hpl hs1
    have hrho := rhoHat_spec p.h a.2
    have hb0' : 0 ≤ bb s := bb_nonneg hs0 hs1
    have hup : bb s ≤ (bbUp p.kb lo.1 lo.2 : ℝ) / 2 ^ p.kb := by
      unfold bbUp; push_cast; linarith
    calc |((a.2 : ℚ) : ℝ)| * bb s ≤ ((rhoHat p.h a.2 : ℝ) / 2 ^ p.h) * ((bbUp p.kb lo.1 lo.2 : ℝ) / 2 ^ p.kb) :=
          mul_le_mul hrho hup hb0' (by positivity)
      _ = _ := by push_cast; rw [pow_add]; field_simp
  · rw [if_neg hb]; positivity

/-! ### All pairs, and the bin masses -/

def pairsAll (p : BinPar) (E : List Ev) (G : List (ℤ × ℤ × ℚ)) : List (ℕ × ℕ) :=
  E.flatMap (atomPairs p) ++ G.flatMap (segPairs p)

theorem pv_flatMap {α : Type*} (L : List α) (f : α → List (ℕ × ℕ)) (j : ℕ) :
    pv (L.flatMap f) j = (L.map fun x => pv (f x) j).sum := by
  induction L with
  | nil => simp [pv_nil]
  | cons x L ih => simp [List.flatMap_cons, pv_append, ih]

theorem sum_map_div {α : Type*} (L : List α) (f : α → ℕ) (d : ℝ) :
    (L.map fun x => (f x : ℝ) / d).sum = (((L.map f).sum : ℕ) : ℝ) / d := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring

/-- The bin masses of the chain profile of `E` are bounded by the pair values. -/
theorem binUp_pilot (p : BinPar) (hB : 1 ≤ p.B) (E : List Ev) (G : List (ℤ × ℤ × ℚ))
    (hE : ∀ e ∈ E, atomOK p e = true)
    (hG : ∀ g ∈ G, 2000000000000 ≤ g.1 ∧ g.1 < g.2.1 ∧ segOK p g = true)
    (hgrid : ∀ j, 1 ≤ j → j ≤ p.B → sqOK (bbN j p.B p.kb) = true) (j : ℕ) (hj : j < p.B) :
    binUp p.B (G.map segR) (E.map atomR) j ≤ (pv (pairsAll p E G) j : ℝ) / 2 ^ (p.kb + p.h) := by
  unfold binUp pairsAll
  rw [pv_append, pv_flatMap, pv_flatMap]
  rw [show ∀ a b : ℕ, ((a + b : ℕ) : ℝ) / 2 ^ (p.kb + p.h) =
      (a : ℝ) / 2 ^ (p.kb + p.h) + (b : ℝ) / 2 ^ (p.kb + p.h) from fun a b => by push_cast; ring]
  rw [← sum_map_div, ← sum_map_div]
  refine add_le_add ?_ ?_
  · rw [List.map_map]
    apply list_sum_le
    intro e he
    have := atom_term p hB e (hE e he) j
    exact this
  · rw [List.map_map]
    apply list_sum_le
    intro g hg
    obtain ⟨h1, h2, h3⟩ := hG g hg
    have := seg_term p hB g h1 h2 h3 hgrid j hj
    exact this

/-! ### The convolution guard on the pair list -/

def hornerPack (R : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + R * hornerPack R l

theorem horner_range (R : ℕ) : ∀ (n : ℕ) (f : ℕ → ℕ),
    hornerPack R ((List.range n).map f) = ∑ i ∈ Finset.range n, f i * R ^ i
  | 0, f => by simp [hornerPack]
  | n + 1, f => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, hornerPack,
      horner_range R n (f ∘ Nat.succ), Finset.sum_range_succ']
    simp only [Function.comp_apply, pow_zero, mul_one, pow_succ]
    rw [Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- The distance kernel, `⌈2^64 min(1, B/(N (d-1)))⌉`. -/
def Kn (N B d : ℕ) : ℕ :=
  if d ≤ 1 then 2 ^ 64 else min (2 ^ 64) ((2 ^ 64 * B + N * (d - 1) - 1) / (N * (d - 1)))

theorem Kn_le (N B d : ℕ) : Kn N B d ≤ 2 ^ 64 := by
  unfold Kn
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem kk_le_Kn {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B) (d : ℕ) :
    kk N B d ≤ (Kn N B d : ℝ) / 2 ^ 64 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have h64 : (0 : ℝ) < 2 ^ 64 := by positivity
  unfold kk kap Kn
  by_cases hd : d ≤ 1
  · have : d - 1 = 0 := by omega
    rw [if_pos hd, this]
    simp
    norm_num
  · rw [if_neg hd]
    have hd2 : 1 ≤ d - 1 := by omega
    set c := N * (d - 1) with hc
    have hc1 : 1 ≤ c := Nat.mul_le_mul hN hd2
    have hcr : (0 : ℝ) < c := by exact_mod_cast hc1
    have hx : (N : ℝ) * (((d - 1 : ℕ) : ℝ) / B) = (c : ℝ) / B := by
      rw [hc]; push_cast; ring
    rw [hx]
    obtain ⟨q, hq⟩ : ∃ q, q = (2 ^ 64 * B + c - 1) / c := ⟨_, rfl⟩
    rw [← hq]
    have hqc : 2 ^ 64 * B ≤ c * q := by
      have h := Nat.lt_mul_div_succ (2 ^ 64 * B + c - 1) (show 0 < c by omega)
      rw [← hq, mul_add, mul_one] at h
      omega
    have hqr : (2 : ℝ) ^ 64 * B ≤ c * q := by exact_mod_cast hqc
    have A1 : 1 / max 1 ((c : ℝ) / B) ≤ (18446744073709551616 : ℝ) / 2 ^ 64 := by
      rw [show (18446744073709551616 : ℝ) = 2 ^ 64 by norm_num, div_self h64.ne']
      exact (div_le_one (lt_of_lt_of_le one_pos (le_max_left _ _))).2 (le_max_left _ _)
    have A2 : 1 / max 1 ((c : ℝ) / B) ≤ (q : ℝ) / 2 ^ 64 := by
      have hcB : 0 < (c : ℝ) / B := by positivity
      calc 1 / max 1 ((c : ℝ) / B) ≤ 1 / ((c : ℝ) / B) :=
            one_div_le_one_div_of_le hcB (le_max_right _ _)
        _ = B / c := by rw [one_div_div]
        _ ≤ q / 2 ^ 64 := by
          rw [div_le_div_iff₀ hcr h64]
          nlinarith
    push_cast [Nat.cast_min]
    rw [← min_div_div_right h64.le]
    exact le_min A1 A2

/-- All finite checks of the packed convolution guard for the pair list `L`. -/
def hvCheck (p : BinPar) (N w M : ℕ) (L : List (ℕ × ℕ)) : Bool :=
  L.all (fun q => decide (q.1 < p.B)) && decide (M < 2 ^ w) &&
  decide (2 ^ 64 * (L.map Prod.snd).sum < 2 ^ w) &&
  decide (((hornerPack (2 ^ (w + 1))
        ((List.range (2 * p.B)).map fun e => Kn N p.B (bdist e (p.B - 1))) *
      (L.map fun q => q.2 * (2 ^ (w + 1)) ^ q.1).sum) / (2 ^ (w + 1)) ^ (p.B - 1) %
        (2 ^ (w + 1)) ^ p.B +
      (2 ^ w - 1 - M) * (((2 ^ (w + 1)) ^ p.B - 1) / (2 ^ (w + 1) - 1))) &&&
    (2 ^ w * (((2 ^ (w + 1)) ^ p.B - 1) / (2 ^ (w + 1) - 1))) = 0)

theorem pilot_conv (p : BinPar) (N w M : ℕ) (L : List (ℕ × ℕ)) (hB : 1 ≤ p.B)
    (h : hvCheck p N w M L = true) :
    (∀ q ∈ L, q.1 < p.B) ∧
      ∀ i < p.B, ∑ j ∈ Finset.range p.B, Kn N p.B (bdist i j) * pv L j ≤ M := by
  unfold hvCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hk, hM⟩, hmass⟩, hg⟩ := h
  refine ⟨hk, ?_⟩
  have hR : 2 ≤ 2 ^ (w + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (w + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  apply conv_guard w hB (Kn N p.B) (pv L) hM (Kmax := 2 ^ 64)
  · intro e _; exact Kn_le _ _ _
  · have e : ∑ j ∈ Finset.range p.B, pv L j = (L.map Prod.snd).sum := by
      have := sum_pairs L hk (fun _ => 1)
      simpa using this.symm
    rw [e]; exact hmass
  · rw [← horner_range, ← sum_pairs L hk (fun j => (2 ^ (w + 1)) ^ j), Nat.geomSum_eq hR]
    exact hg

/-! ### The instance -/

def pilotP : BinPar := ⟨4096, 64, 64, 64⟩

/-- The pair list of the negative row (same-sign gas difference). -/
def pilotPairs : List (ℕ × ℕ) := pairsAll pilotP EsQ (chainQ 0 EsQ)

/-- `M` : the exact maximum convolution digit (integer arithmetic mirrored in Python). -/
def pilotM : ℕ := 221412481437836064751019615489095128669015654676947969571

def pilotBinChecks : Bool :=
  gridOK pilotP && EsQ.all (atomOK pilotP) && (chainQ 0 EsQ).all (segOK pilotP) &&
  hvCheck pilotP 2048 200 pilotM pilotPairs

-- kcost: 4096 grid roots + 4272 pairs x 2 roots + 279 x 2 + 278 x 4 roots, each Newton ~12 steps
-- (about 40 ops), plus packing (12k Horner steps, 4.3k pair terms) and one product of
-- 1 Mbit numbers: about 0.6 M kernel ops, estimated 25 s
theorem pilot_bin_checks : pilotBinChecks = true := by decide +kernel

/-- **The spatial bounded-variation tail of the negative row.** -/
theorem pilot_hV : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    dirV 2048 pilotW.Ps pilotW.Es t ≤ (pilotM : ℝ) / (2 ^ 64 * 2 ^ (64 + 64)) := by
  have hc := pilot_checks
  simp only [pilotChecks, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsEs, hsEo⟩, hsEc⟩, ha1⟩, ha2⟩, ha3⟩, hb1⟩, hb2⟩, hb3⟩ := hc
  have hb := pilot_bin_checks
  simp only [pilotBinChecks, Bool.and_eq_true, List.all_eq_true] at hb
  obtain ⟨⟨⟨hgrid, hat⟩, hseg⟩, hv⟩ := hb
  have hB : 1 ≤ pilotP.B := by decide
  obtain ⟨hkeys, hconv⟩ := pilot_conv pilotP 2048 200 pilotM pilotPairs hB hv
  have hok := pilot_ok
  have hbin : ∀ j < pilotP.B, binUp pilotP.B pilotW.Ps pilotW.Es j ≤
      (pv pilotPairs j : ℝ) / 2 ^ (pilotP.kb + pilotP.h) := by
    intro j hj
    refine binUp_pilot pilotP hB EsQ (chainQ 0 EsQ) hat ?_ (gridOK_spec hgrid) j hj
    intro g hg
    obtain ⟨h1, h2, h3⟩ := chain_bounds EsQ 0 ha1 hb1 g hg
    exact ⟨h2, h1, hseg g hg⟩
  have := dirV_le_of_packed (N := 2048) (B := 4096) (by decide) hok.supp_s hok.atoms_y
    (Kn := Kn 2048 4096) (mn := pv pilotPairs) (dK := 2 ^ 64) (dm := 2 ^ (pilotP.kb + pilotP.h))
    (by positivity) (by positivity)
    (fun d _ => kk_le_Kn (by norm_num) (by norm_num) d) hbin hconv
  simpa [pilotP] using this

/-- The spatial bound of the negative row, as the real `Mx`. -/
def pilotMx : ℝ := (pilotM : ℝ) / (2 ^ 64 * 2 ^ (64 + 64))

/-! ### A fixed-point logarithm with a rigorous error: `log w = 2 atanh ((w-1)/(w+1))` -/

theorem atanh_partial (s : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), (s ^ (i + 1) / ((i : ℝ) + 1) - (-s) ^ (i + 1) / ((i : ℝ) + 1)) =
      2 * ∑ j ∈ Finset.range n, s ^ (2 * j + 1) / (2 * (j : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have e1 : (-s) ^ (2 * n + 1 + 1) = s ^ (2 * n + 1 + 1) := Even.neg_pow ⟨n + 1, by ring⟩ s
    have e2 : (-s) ^ (2 * n + 1) = - s ^ (2 * n + 1) := Odd.neg_pow ⟨n, rfl⟩ s
    rw [e1, e2]
    push_cast
    ring

theorem log_ratio_series {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) (n : ℕ) :
    |Real.log (1 + s) - Real.log (1 - s) -
        2 * ∑ j ∈ Finset.range n, s ^ (2 * j + 1) / (2 * (j : ℝ) + 1)| ≤
      2 * (s ^ (2 * n + 1) / (1 - s)) := by
  have hs : |s| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hs' : |-s| < 1 := by rw [abs_neg]; exact hs
  have a1 := Real.abs_log_sub_add_sum_range_le hs (2 * n)
  have a2 := Real.abs_log_sub_add_sum_range_le hs' (2 * n)
  rw [abs_neg, abs_of_nonneg h0] at a2
  rw [abs_of_nonneg h0] at a1
  rw [← atanh_partial, Finset.sum_sub_distrib]
  have e : (1 + s) = 1 - (-s) := by ring
  rw [e]
  have b1 := abs_le.mp a1
  have b2 := abs_le.mp a2
  rw [abs_le]
  constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2]

/-- The power loop of the fixed-point `atanh` series. -/
def atLoop (a2 b2 : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | n + 1, j, p, acc => atLoop a2 b2 n (j + 1) (p * a2 / b2) (acc + p / (2 * j + 1))

theorem atLoop_spec {s : ℝ} {a2 b2 : ℕ} (R : ℝ) (hR : 0 ≤ R) (hb2 : 0 < b2) (hs0 : 0 ≤ s)
    (hs2 : s ^ 2 = (a2 : ℝ) / b2) (hs4 : s ^ 2 ≤ 1 / 4) :
    ∀ (n j p acc : ℕ), |(p : ℝ) - R * s ^ (2 * j + 1)| ≤ 2 →
      |(atLoop a2 b2 n j p acc : ℝ) -
          ((acc : ℝ) + R * ∑ i ∈ Finset.range n,
            s ^ (2 * (j + i) + 1) / ((2 * (j + i) + 1 : ℕ) : ℝ))| ≤ 3 * n
  | 0, j, p, acc, _ => by simp [atLoop]
  | n + 1, j, p, acc, hp => by
    have hb2r : (0 : ℝ) < b2 := by exact_mod_cast hb2
    have hp' : |((p * a2 / b2 : ℕ) : ℝ) - R * s ^ (2 * (j + 1) + 1)| ≤ 2 := by
      have hfl : ((p * a2 / b2 : ℕ) : ℝ) ≤ ((p * a2 : ℕ) : ℝ) / b2 := Nat.cast_div_le
      have hfl2 : ((p * a2 : ℕ) : ℝ) / b2 < ((p * a2 / b2 : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hb2r]
        have := Nat.lt_mul_div_succ (p * a2) hb2
        have h' : ((p * a2 : ℕ) : ℝ) < b2 * (((p * a2 / b2 : ℕ) : ℝ) + 1) := by exact_mod_cast this
        linarith
      have e : R * s ^ (2 * (j + 1) + 1) = (R * s ^ (2 * j + 1)) * s ^ 2 := by
        rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, pow_add]; ring
      have e2 : ((p * a2 : ℕ) : ℝ) / b2 = (p : ℝ) * s ^ 2 := by
        rw [hs2]; push_cast; ring
      have h3 : |(p : ℝ) * s ^ 2 - (R * s ^ (2 * j + 1)) * s ^ 2| ≤ 1 / 2 := by
        rw [← sub_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ s ^ 2)]
        nlinarith [abs_nonneg ((p : ℝ) - R * s ^ (2 * j + 1)), sq_nonneg s]
      rw [e]
      rw [abs_le] at h3 ⊢
      constructor <;> nlinarith [h3.1, h3.2]
    have ih := atLoop_spec R hR hb2 hs0 hs2 hs4 n (j + 1) (p * a2 / b2) (acc + p / (2 * j + 1)) hp'
    have hq : |((p / (2 * j + 1) : ℕ) : ℝ) - R * s ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)| ≤ 3 := by
      have hd : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by positivity
      have hfl : ((p / (2 * j + 1) : ℕ) : ℝ) ≤ (p : ℝ) / ((2 * j + 1 : ℕ) : ℝ) := Nat.cast_div_le
      have hfl2 : (p : ℝ) / ((2 * j + 1 : ℕ) : ℝ) < ((p / (2 * j + 1) : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hd]
        have := Nat.lt_mul_div_succ p (show 0 < 2 * j + 1 by omega)
        have h' : (p : ℝ) < ((2 * j + 1 : ℕ) : ℝ) * (((p / (2 * j + 1) : ℕ) : ℝ) + 1) := by
          exact_mod_cast this
        linarith
      have hpd : |(p : ℝ) / ((2 * j + 1 : ℕ) : ℝ) - R * s ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)| ≤ 2 := by
        rw [← sub_div, abs_div, abs_of_pos hd, div_le_iff₀ hd]
        have h1 : (1 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * j + 1)
        nlinarith [hp, abs_nonneg ((p : ℝ) - R * s ^ (2 * j + 1))]
      rw [abs_le] at hpd ⊢
      constructor <;> nlinarith [hpd.1, hpd.2]
    rw [Finset.sum_range_succ', atLoop]
    have e3 : ∀ i : ℕ, 2 * (j + (i + 1)) + 1 = 2 * (j + 1 + i) + 1 := fun i => by ring
    simp only [e3, add_zero]
    push_cast at ih hq ⊢
    rw [mul_add, ← mul_div_assoc]
    rw [abs_le] at ih hq ⊢
    constructor <;> nlinarith [ih.1, ih.2, hq.1, hq.2]

def atanhV (F n a b : ℕ) : ℕ := 2 * atLoop (a * a) (b * b) n 0 (2 ^ F * a / b) 0

theorem atanhV_spec {F n a b : ℕ} (hb : 0 < b) (hab : 2 * a ≤ b) :
    |Real.log (((b : ℝ) + a) / ((b : ℝ) - a)) - (atanhV F n a b : ℝ) / 2 ^ F| ≤
      6 * n / 2 ^ F + 2 * (((a : ℝ) / b) ^ (2 * n + 1) / (1 - (a : ℝ) / b)) := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hR : (0 : ℝ) < 2 ^ F := by positivity
  have hab' : 2 * (a : ℝ) ≤ b := by exact_mod_cast hab
  set s : ℝ := (a : ℝ) / b with hs
  have hs0 : 0 ≤ s := by positivity
  have hs2 : s < 1 := by
    rw [hs, div_lt_one hbr]
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    nlinarith [hbr]
  have hss : s ^ 2 = ((a * a : ℕ) : ℝ) / ((b * b : ℕ) : ℝ) := by
    rw [hs]; push_cast; ring
  have hs4 : s ^ 2 ≤ 1 / 4 := by
    rw [hs, div_pow, div_le_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) a]
  have hp0 : |(((2 ^ F * a / b : ℕ)) : ℝ) - 2 ^ F * s ^ (2 * 0 + 1)| ≤ 2 := by
    have hfl : (((2 ^ F * a / b : ℕ)) : ℝ) ≤ ((2 ^ F * a : ℕ) : ℝ) / b := Nat.cast_div_le
    have hfl2 : ((2 ^ F * a : ℕ) : ℝ) / b < (((2 ^ F * a / b : ℕ)) : ℝ) + 1 := by
      rw [div_lt_iff₀ hbr]
      have := Nat.lt_mul_div_succ (2 ^ F * a) hb
      have h' : ((2 ^ F * a : ℕ) : ℝ) < b * ((((2 ^ F * a / b : ℕ)) : ℝ) + 1) := by exact_mod_cast this
      linarith
    have e : ((2 ^ F * a : ℕ) : ℝ) / b = 2 ^ F * s ^ (2 * 0 + 1) := by
      rw [hs]; push_cast; ring
    rw [abs_le]; constructor <;> linarith
  have key := atLoop_spec (2 ^ F : ℝ) hR.le (by positivity : 0 < b * b) hs0 hss hs4 n 0 (2 ^ F * a / b) 0 hp0
  have hlog : Real.log (((b : ℝ) + a) / ((b : ℝ) - a)) = Real.log (1 + s) - Real.log (1 - s) := by
    have h1 : (0 : ℝ) < 1 + s := by linarith
    have h2 : (0 : ℝ) < 1 - s := by linarith
    rw [← Real.log_div h1.ne' h2.ne']
    congr 1
    rw [hs]
    have hba : (0 : ℝ) < b - a := by linarith
    field_simp
  have ser := log_ratio_series hs0 hs2 n
  have hsum : ∑ i ∈ Finset.range n, s ^ (2 * (0 + i) + 1) / ((2 * (0 + i) + 1 : ℕ) : ℝ) =
      ∑ j ∈ Finset.range n, s ^ (2 * j + 1) / (2 * (j : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  rw [hsum] at key
  unfold atanhV
  rw [hlog]
  push_cast
  have e4 : (2 * (atLoop (a * a) (b * b) n 0 (2 ^ F * a / b) 0 : ℝ)) / 2 ^ F =
      2 * ((atLoop (a * a) (b * b) n 0 (2 ^ F * a / b) 0 : ℝ) / 2 ^ F) := by ring
  rw [e4]
  set acc : ℝ := (atLoop (a * a) (b * b) n 0 (2 ^ F * a / b) 0 : ℝ)
  set S : ℝ := ∑ j ∈ Finset.range n, s ^ (2 * j + 1) / (2 * (j : ℝ) + 1)
  have k1 : |acc / 2 ^ F - S| ≤ 3 * n / 2 ^ F := by
    have e5 : acc / 2 ^ F - S = (acc - (((0 : ℕ) : ℝ) + 2 ^ F * S)) / 2 ^ F := by
      push_cast; field_simp; ring
    rw [e5, abs_div, abs_of_pos hR]
    exact div_le_div_of_nonneg_right key hR.le
  rw [abs_le] at k1 ser ⊢
  have e6 : (6 : ℝ) * n / 2 ^ F = 2 * (3 * n / 2 ^ F) := by ring
  rw [e6]
  constructor <;> nlinarith [k1.1, k1.2, ser.1, ser.2]

def lnormAux (m0 : ℤ) (P0 Q0 : ℕ) : ℤ × ℕ × ℕ :=
  if 4 * P0 < 3 * Q0 then (m0 - 1, 2 * P0, Q0)
  else if 3 * Q0 < 2 * P0 then (m0 + 1, P0, 2 * Q0) else (m0, P0, Q0)

/-- `P / Q = 2^m * (P1 / Q1)` with `3/4 <= P1/Q1 <= 3/2`. -/
def lnorm (P Q : ℕ) : ℤ × ℕ × ℕ :=
  lnormAux ((P.log2 : ℤ) - (Q.log2 : ℤ)) (P <<< (-((P.log2 : ℤ) - (Q.log2 : ℤ))).toNat)
    (Q <<< ((P.log2 : ℤ) - (Q.log2 : ℤ)).toNat)

theorem lnormAux_rel (m0 : ℤ) (P0 Q0 : ℕ) (hQ0 : 0 < Q0) :
    (2 : ℝ) ^ m0 * ((P0 : ℝ) / Q0) =
      (2 : ℝ) ^ (lnormAux m0 P0 Q0).1 * (((lnormAux m0 P0 Q0).2.1 : ℝ) / (lnormAux m0 P0 Q0).2.2) := by
  have hq : (0 : ℝ) < Q0 := by exact_mod_cast hQ0
  unfold lnormAux
  split_ifs
  · simp only
    rw [zpow_sub₀ (by norm_num), zpow_one]
    push_cast
    field_simp
  · simp only
    rw [zpow_add₀ (by norm_num), zpow_one]
    push_cast
    field_simp
  · rfl

theorem lnorm_rel (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q) :
    (P : ℝ) / Q = (2 : ℝ) ^ (lnorm P Q).1 * (((lnorm P Q).2.1 : ℝ) / (lnorm P Q).2.2) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have core : ∀ m0 : ℤ, (P : ℝ) / Q =
      (2 : ℝ) ^ m0 * (((P <<< (-m0).toNat : ℕ) : ℝ) / ((Q <<< m0.toNat : ℕ) : ℝ)) := by
    intro m0
    rcases Int.eq_nat_or_neg m0 with ⟨t, rfl | rfl⟩
    · have h1 : (-(t : ℤ)).toNat = 0 := by omega
      have h2 : ((t : ℤ)).toNat = t := by omega
      rw [h1, h2, Nat.shiftLeft_eq, Nat.shiftLeft_eq, zpow_natCast]
      push_cast
      field_simp
    · have h1 : (-(-(t : ℤ))).toNat = t := by omega
      have h2 : (-(t : ℤ)).toNat = 0 := by omega
      rw [h1, h2, Nat.shiftLeft_eq, Nat.shiftLeft_eq, zpow_neg, zpow_natCast]
      push_cast
      field_simp
  have hQ0 : 0 < (Q <<< (((P.log2 : ℤ) - (Q.log2 : ℤ)).toNat)) := by
    rw [Nat.shiftLeft_eq]; positivity
  unfold lnorm
  rw [core ((P.log2 : ℤ) - (Q.log2 : ℤ))]
  exact lnormAux_rel _ _ _ hQ0

def lnormOK (P Q : ℕ) : Bool :=
  decide (3 * (lnorm P Q).2.2 ≤ 4 * (lnorm P Q).2.1 ∧ 2 * (lnorm P Q).2.1 ≤ 3 * (lnorm P Q).2.2)

def logFx (F n n2 P Q : ℕ) : ℤ :=
  let t := lnorm P Q
  let ln2 : ℤ := atanhV F n2 1 3
  let w : ℤ := if t.2.2 ≤ t.2.1 then (atanhV F n (t.2.1 - t.2.2) (t.2.1 + t.2.2) : ℤ)
    else -(atanhV F n (t.2.2 - t.2.1) (t.2.1 + t.2.2) : ℤ)
  t.1 * ln2 + w

theorem tail_le {s : ℝ} (h0 : 0 ≤ s) (h5 : s ≤ 1 / 5) (n : ℕ) :
    2 * (s ^ (2 * n + 1) / (1 - s)) ≤ 5 / 2 * (1 / 5 : ℝ) ^ (2 * n + 1) := by
  have h1 : s ^ (2 * n + 1) ≤ (1 / 5 : ℝ) ^ (2 * n + 1) := pow_le_pow_left₀ h0 h5 _
  have h2 : s ^ (2 * n + 1) / (1 - s) ≤ (1 / 5 : ℝ) ^ (2 * n + 1) / (4 / 5) := by
    apply div_le_div₀ (by positivity) h1 (by norm_num) (by linarith)
  have e : (1 / 5 : ℝ) ^ (2 * n + 1) / (4 / 5) = 5 / 4 * (1 / 5 : ℝ) ^ (2 * n + 1) := by ring
  rw [e] at h2
  linarith

theorem ln2_enc (F n2 : ℕ) :
    |Real.log 2 - (atanhV F n2 1 3 : ℝ) / 2 ^ F| ≤ 6 * n2 / 2 ^ F + 3 * (1 / 3 : ℝ) ^ (2 * n2 + 1) := by
  have h := atanhV_spec (F := F) (n := n2) (a := 1) (b := 3) (by norm_num) (by norm_num)
  have e : Real.log ((((3 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) / (((3 : ℕ) : ℝ) - ((1 : ℕ) : ℝ))) = Real.log 2 := by
    norm_num
  have t : 2 * ((((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) ^ (2 * n2 + 1) / (1 - ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ))) =
      3 * (1 / 3 : ℝ) ^ (2 * n2 + 1) := by
    norm_num; ring
  rw [e, t] at h
  exact h

/-- The logarithm of the normalised ratio, as a signed fixed-point number. -/
theorem logw_enc {F n P1 Q1 : ℕ} (hP1 : 0 < P1) (hQ1 : 0 < Q1) (h34 : 3 * Q1 ≤ 4 * P1)
    (h32 : 2 * P1 ≤ 3 * Q1) :
    |Real.log ((P1 : ℝ) / Q1) -
        ((if Q1 ≤ P1 then (atanhV F n (P1 - Q1) (P1 + Q1) : ℤ) else -(atanhV F n (Q1 - P1) (P1 + Q1) : ℤ) : ℤ) : ℝ) / 2 ^ F| ≤
      6 * n / 2 ^ F + 5 / 2 * (1 / 5 : ℝ) ^ (2 * n + 1) := by
  have hP1r : (0 : ℝ) < P1 := by exact_mod_cast hP1
  have hQ1r : (0 : ℝ) < Q1 := by exact_mod_cast hQ1
  have hP1ne : (P1 : ℝ) ≠ 0 := hP1r.ne'
  have hQ1ne : (Q1 : ℝ) ≠ 0 := hQ1r.ne'
  split_ifs with hle
  · have hab : 2 * (P1 - Q1) ≤ P1 + Q1 := by omega
    have h := atanhV_spec (F := F) (n := n) (a := P1 - Q1) (b := P1 + Q1) (by omega) hab
    have hs5 : ((P1 - Q1 : ℕ) : ℝ) / ((P1 + Q1 : ℕ) : ℝ) ≤ 1 / 5 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 5 * (P1 - Q1) ≤ P1 + Q1 := by omega
      exact_mod_cast (by omega : (P1 - Q1) * 5 ≤ 1 * (P1 + Q1))
    have ht := tail_le (by positivity) hs5 n
    have e : (((P1 + Q1 : ℕ) : ℝ) + ((P1 - Q1 : ℕ) : ℝ)) / (((P1 + Q1 : ℕ) : ℝ) - ((P1 - Q1 : ℕ) : ℝ)) =
        (P1 : ℝ) / Q1 := by
      rw [Nat.cast_sub hle]; push_cast
      have h1 : ((P1 : ℝ) + Q1 + (P1 - Q1)) = 2 * P1 := by ring
      have h2 : ((P1 : ℝ) + Q1 - (P1 - Q1)) = 2 * Q1 := by ring
      rw [h1, h2]; field_simp
    rw [e] at h
    push_cast
    rw [abs_le] at h ⊢
    constructor <;> nlinarith [h.1, h.2, ht]
  · have hlt : P1 < Q1 := by omega
    have hab : 2 * (Q1 - P1) ≤ P1 + Q1 := by omega
    have h := atanhV_spec (F := F) (n := n) (a := Q1 - P1) (b := P1 + Q1) (by omega) hab
    have hs5 : ((Q1 - P1 : ℕ) : ℝ) / ((P1 + Q1 : ℕ) : ℝ) ≤ 1 / 5 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      exact_mod_cast (by omega : (Q1 - P1) * 5 ≤ 1 * (P1 + Q1))
    have ht := tail_le (by positivity) hs5 n
    have e : (((P1 + Q1 : ℕ) : ℝ) + ((Q1 - P1 : ℕ) : ℝ)) / (((P1 + Q1 : ℕ) : ℝ) - ((Q1 - P1 : ℕ) : ℝ)) =
        (Q1 : ℝ) / P1 := by
      rw [Nat.cast_sub hlt.le]; push_cast
      have h1 : ((P1 : ℝ) + Q1 + (Q1 - P1)) = 2 * Q1 := by ring
      have h2 : ((P1 : ℝ) + Q1 - (Q1 - P1)) = 2 * P1 := by ring
      rw [h1, h2]; field_simp
    rw [e] at h
    have hl : Real.log ((P1 : ℝ) / Q1) = - Real.log ((Q1 : ℝ) / P1) := by
      rw [← Real.log_inv, inv_div]
    rw [hl]
    push_cast
    simp only [neg_div]
    rw [abs_le] at h ⊢
    constructor <;> nlinarith [h.1, h.2, ht]

theorem logFx_spec {F n n2 P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q) (hok : lnormOK P Q = true) :
    |Real.log ((P : ℝ) / Q) - (logFx F n n2 P Q : ℝ) / 2 ^ F| ≤
      |((lnorm P Q).1 : ℝ)| * (6 * n2 / 2 ^ F + 3 * (1 / 3 : ℝ) ^ (2 * n2 + 1)) +
        (6 * n / 2 ^ F + 5 / 2 * (1 / 5 : ℝ) ^ (2 * n + 1)) := by
  have hrel := lnorm_rel P Q hP hQ
  unfold lnormOK at hok
  rw [decide_eq_true_eq] at hok
  unfold logFx
  rcases hl : lnorm P Q with ⟨m, P1, Q1⟩
  simp only [hl] at hrel hok ⊢
  obtain ⟨h34, h32⟩ := hok
  have hPQ : (0 : ℝ) < (P : ℝ) / Q := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hpos : 0 < (P1 : ℝ) / Q1 := by
    rw [hrel] at hPQ
    exact (mul_pos_iff_of_pos_left h2).1 hPQ
  have hP1 : 0 < P1 := by
    by_contra h0
    have : P1 = 0 := by omega
    rw [this] at hpos; simp at hpos
  have hQ1 : 0 < Q1 := by
    by_contra h0
    have : Q1 = 0 := by omega
    rw [this] at hpos; simp at hpos
  have hlog : Real.log ((P : ℝ) / Q) = (m : ℝ) * Real.log 2 + Real.log ((P1 : ℝ) / Q1) := by
    rw [hrel, Real.log_mul h2.ne' hpos.ne', Real.log_zpow]
  have a1 := ln2_enc F n2
  have a2 := logw_enc (F := F) (n := n) hP1 hQ1 h34 h32
  rw [hlog]
  obtain ⟨ln2Z, hln2Z⟩ : ∃ z : ℤ, z = (atanhV F n2 1 3 : ℤ) := ⟨_, rfl⟩
  obtain ⟨wZ, hwZ⟩ : ∃ z : ℤ, z = (if Q1 ≤ P1 then (atanhV F n (P1 - Q1) (P1 + Q1) : ℤ)
      else -(atanhV F n (Q1 - P1) (P1 + Q1) : ℤ)) := ⟨_, rfl⟩
  rw [← hln2Z, ← hwZ]
  rw [← hwZ] at a2
  have a1' : |Real.log 2 - (ln2Z : ℝ) / 2 ^ F| ≤ 6 * n2 / 2 ^ F + 3 * (1 / 3 : ℝ) ^ (2 * n2 + 1) := by
    rw [hln2Z]; push_cast; exact a1
  have e : (m : ℝ) * Real.log 2 + Real.log ((P1 : ℝ) / Q1) - ((m * ln2Z + wZ : ℤ) : ℝ) / 2 ^ F =
      (m : ℝ) * (Real.log 2 - (ln2Z : ℝ) / 2 ^ F) + (Real.log ((P1 : ℝ) / Q1) - (wZ : ℝ) / 2 ^ F) := by
    push_cast; ring
  rw [e]
  calc |(m : ℝ) * (Real.log 2 - (ln2Z : ℝ) / 2 ^ F) + (Real.log ((P1 : ℝ) / Q1) - (wZ : ℝ) / 2 ^ F)|
      ≤ |(m : ℝ) * (Real.log 2 - (ln2Z : ℝ) / 2 ^ F)| + |Real.log ((P1 : ℝ) / Q1) - (wZ : ℝ) / 2 ^ F| :=
        abs_add_le _ _
    _ ≤ |(m : ℝ)| * (6 * n2 / 2 ^ F + 3 * (1 / 3 : ℝ) ^ (2 * n2 + 1)) +
          (6 * n / 2 ^ F + 5 / 2 * (1 / 5 : ℝ) ^ (2 * n + 1)) := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left a1' (abs_nonneg _)) a2

#print axioms pilot_ok
#print axioms pilot_hV
#print axioms logFx_spec

end

end CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
