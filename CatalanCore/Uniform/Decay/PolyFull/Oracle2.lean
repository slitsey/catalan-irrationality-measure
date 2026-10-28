import CatalanCore.Uniform.Decay.PairEnergy.PairSound
import CatalanCore.Uniform.Decay.NearCells.Eval
import CatalanCore.Uniform.Decay.Cells.Energy
set_option Elab.async false

/-!
# Pair-energy oracle on the current D6b evaluators (lane D, package D10)

`PairEnergy/Enc.lean` and `PairEnergy/Oracle.lean` (D6c) were written against an earlier
`argEnc_sound` (hypothesis `w.im ≠ 0`); D6b has since proved `argEnc_sound` unconditionally.  This
module repeats `encAtom`, `termsUb`, `pairUb`, `pairCheck`, `pairOk` and `pairOracle` verbatim apart
from that one change, in the namespace `PolyFull`, so that D10 does not depend on the stale D6c
`Enc`.  The statements and proofs are those of D6c.
-/

namespace CatalanCore.Uniform.Decay.PolyFull

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PairEnergy

def toCQ (w : QC) : CQ := ⟨w.re, w.im⟩

theorem toCQ_toC (w : QC) : (toCQ w).toC = w.toC := rfl

/-- Centre and radius of an atom enclosure. -/
def encAtom : Atom → Option (ℚ × ℚ)
  | .logC w => if w.nsq = 0 then some (0, 0) else logHalf (toCQ w)
  | .argC w => argEnc (toCQ w)

theorem encAtom_sound {a : Atom} {c ε : ℚ} (h : encAtom a = some (c, ε)) :
    |(c : ℝ) - a.val| ≤ ε := by
  cases a with
  | logC w =>
    simp only [encAtom] at h
    split_ifs at h with hw
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hre : w.re = 0 ∧ w.im = 0 := by
        unfold QC.nsq at hw
        constructor <;> nlinarith [mul_self_nonneg w.re, mul_self_nonneg w.im]
      have : w.toC = 0 := by apply Complex.ext <;> simp [QC.toC, hre.1, hre.2]
      simp [Atom.val, this]
    · have := logHalf_sound (w := toCQ w) (by simpa [toCQ, CQ.nsq, QC.nsq] using hw) h
      simpa [Atom.val, toCQ_toC] using this
  | argC w =>
    simp only [encAtom] at h
    have := argEnc_sound (w := toCQ w) h
    simpa [Atom.val, toCQ_toC] using this

def termsUb : List (ℚ × Atom) → Option ℚ
  | [] => some 0
  | (q, a) :: l =>
    match encAtom a, termsUb l with
    | some (c, ε), some r => some (q * c + |q| * ε + r)
    | _, _ => none

theorem termsUb_sound {l : List (ℚ × Atom)} {u : ℚ} (h : termsUb l = some u) :
    termsVal l ≤ (u : ℝ) := by
  induction l generalizing u with
  | nil => simp [termsUb] at h; subst h; simp [termsVal]
  | cons p l ih =>
    obtain ⟨q, a⟩ := p
    simp only [termsUb] at h
    split at h
    · rename_i c ε r hce hr
      simp only [Option.some.injEq] at h; subst h
      have h1 := encAtom_sound hce
      have h2 := ih hr
      rw [abs_le] at h1
      simp only [termsVal]
      push_cast
      have hq : (q : ℝ) * a.val ≤ q * c + |(q : ℝ)| * ε := by
        rcases le_total 0 (q : ℝ) with h0 | h0
        · rw [abs_of_nonneg h0]; nlinarith [h1.1, h1.2]
        · rw [abs_of_nonpos h0]; nlinarith [h1.1, h1.2]
      linarith
    · simp at h

def lfUb (f : LF) : Option ℚ :=
  match termsUb f.terms with
  | some r => some (f.c + r)
  | none => none

theorem lfUb_sound {f : LF} {u : ℚ} (h : lfUb f = some u) : f.val ≤ (u : ℝ) := by
  unfold lfUb at h
  split at h
  · rename_i r hr
    simp only [Option.some.injEq] at h; subst h
    unfold LF.val; push_cast
    linarith [termsUb_sound hr]
  · simp at h

def segA (s : Seg) : QC := ⟨s.ax, s.ay⟩
def segB (s : Seg) : QC := ⟨s.bx, s.byy⟩

def cross (x y : QC) : ℚ := x.re * y.im - x.im * y.re

/-- Pair data with the common point solved (the relation is re-checked by `pairCheck`). -/
def mkPair (s1 s2 : Seg) : PairData :=
  let A1 := segA s1
  let B1 := segB s1
  let A2 := segA s2
  let B2 := segB s2
  let u := QC.sub B1 A1
  let v := QC.sub B2 A2
  let w := QC.sub A1 A2
  let det := cross u v
  if det ≠ 0 then
    ⟨A1, B1, A2, B2, s1.coef, s2.coef, -(cross w v) / det, cross u w / det⟩
  else
    ⟨A1, B1, A2, B2, s1.coef, s2.coef, 0, (w.re * v.re + w.im * v.im) / v.nsq⟩

def pairUb (P : PairData) : Option ℚ := lfUb P.pairLF

def pairCheck (s1 s2 : Seg) (E : ℚ) : Bool :=
  let P := mkPair s1 s2
  decide (P.rel = QC.zero) && decide (QC.sub P.B1 P.A1 ≠ QC.zero) &&
    decide (QC.sub P.B2 P.A2 ≠ QC.zero) &&
    (match pairUb P with
      | some u => decide (u ≤ E)
      | none => false)

theorem QC.toC_eq_zero' {x : QC} (h : x.toC = 0) : x = QC.zero := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [QC.toC] at h1 h2
  cases x; simp_all [QC.zero]

theorem pairCheck_sound {s1 s2 : Seg} {E : ℚ} (h : pairCheck s1 s2 E = true) :
    ∫ s in (0 : ℝ)..1, evalL s1.coef s * ∫ t in (0 : ℝ)..1, evalL s2.coef t *
      (-Real.log ‖((segA s1).toC + (s : ℂ) * ((segB s1).toC - (segA s1).toC)) -
        ((segA s2).toC + (t : ℂ) * ((segB s2).toC - (segA s2).toC))‖) ≤ (E : ℝ) := by
  unfold pairCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hrel, hu⟩, hv⟩, hub⟩ := h
  set P := mkPair s1 s2 with hP
  have hA1 : P.A1 = segA s1 := by simp [hP, mkPair]; split_ifs <;> rfl
  have hB1 : P.B1 = segB s1 := by simp [hP, mkPair]; split_ifs <;> rfl
  have hA2 : P.A2 = segA s2 := by simp [hP, mkPair]; split_ifs <;> rfl
  have hB2 : P.B2 = segB s2 := by simp [hP, mkPair]; split_ifs <;> rfl
  have ha : P.a = s1.coef := by simp [hP, mkPair]; split_ifs <;> rfl
  have hb : P.b = s2.coef := by simp [hP, mkPair]; split_ifs <;> rfl
  have hu' : (QC.sub P.B1 P.A1).toC ≠ 0 := fun h0 => hu (QC.toC_eq_zero' h0)
  have hv' : (QC.sub P.B2 P.A2).toC ≠ 0 := fun h0 => hv (QC.toC_eq_zero' h0)
  have hval := pairLF_val P hu' hv' hrel
  rw [hA1, hB1, hA2, hB2, ha, hb] at hval
  rw [← hval]
  unfold pairUb at hub
  split at hub
  · rename_i u hu2
    simp only [decide_eq_true_eq] at hub
    exact (lfUb_sound hu2).trans (by exact_mod_cast hub)
  · simp at hub

def pairOk (D : SplineData) (i j : ℕ) (E : ℚ) : Bool :=
  match D.segs[i]?, D.segs[j]? with
  | some s1, some s2 => pairCheck s1 s2 E
  | _, _ => false

theorem pairE_eq (D : SplineData) (i j : Fin D.n) :
    pairE D i j = ∫ s in (0 : ℝ)..1, evalL (D.seg i).coef s * ∫ t in (0 : ℝ)..1, evalL (D.seg j).coef t *
      (-Real.log ‖((segA (D.seg i)).toC + (s : ℂ) * ((segB (D.seg i)).toC - (segA (D.seg i)).toC)) -
        ((segA (D.seg j)).toC + (t : ℂ) * ((segB (D.seg j)).toC - (segA (D.seg j)).toC))‖) := by
  unfold pairE segU
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [SplineData.f, SplineData.l, ratPoly_eq_evalL, pt, SplineData.A, SplineData.B,
    segA, segB, QC.toC]

theorem pairOk_sound (D : SplineData) (i j : Fin D.n) (E : ℚ) (h : pairOk D i.1 j.1 E = true) :
    pairE D i j ≤ E := by
  unfold pairOk at h
  rw [List.getElem?_eq_getElem i.2, List.getElem?_eq_getElem j.2] at h
  rw [pairE_eq]
  exact pairCheck_sound h

/-- **The pair-energy oracle** discharging `Cells.PairOracle`. -/
def pairOracle : PairOracle where
  pairOk := pairOk
  pair_sound := fun D _ i j E h => pairOk_sound D i j E h

end CatalanCore.Uniform.Decay.PolyFull
