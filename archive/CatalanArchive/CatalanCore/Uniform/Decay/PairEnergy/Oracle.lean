import CatalanCore.Uniform.Decay.PairEnergy.Enc
import CatalanCore.Uniform.Decay.Cells.Energy
set_option Elab.async false

/-!
# The pair-energy oracle (lane D, package D6c)

`pairCheck s1 s2 E` is the Boolean test "the pair energy of the two segments is `≤ E`":
it solves the common point `(s₀, t₀)` (Cramer, or the projection for collinear segments), checks the
relation exactly in `QC`, and compares the directed upper bound `pairUb`.  `pairOracle` discharges
`Cells.PairOracle`.
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Cells

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

def pairUb (P : PairData) : Option ℚ := P.pairLF.ub

def pairCheck (s1 s2 : Seg) (E : ℚ) : Bool :=
  let P := mkPair s1 s2
  decide (P.rel = QC.zero) && decide (QC.sub P.B1 P.A1 ≠ QC.zero) &&
    decide (QC.sub P.B2 P.A2 ≠ QC.zero) &&
    (match pairUb P with
      | some u => decide (u ≤ E)
      | none => false)

theorem QC.toC_eq_zero {x : QC} (h : x.toC = 0) : x = QC.zero := by
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
  have hu' : (QC.sub P.B1 P.A1).toC ≠ 0 := fun h0 => hu (QC.toC_eq_zero h0)
  have hv' : (QC.sub P.B2 P.A2).toC ≠ 0 := fun h0 => hv (QC.toC_eq_zero h0)
  have hval := pairLF_val P hu' hv' hrel
  rw [hA1, hB1, hA2, hB2, ha, hb] at hval
  rw [← hval]
  unfold pairUb at hub
  split at hub
  · rename_i u hu2
    simp only [decide_eq_true_eq] at hub
    exact (LF.ub_sound hu2).trans (by exact_mod_cast hub)
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

/-- **The pair-energy oracle** discharging `Cells.PairOracle` (and its polygon counterpart). -/
def pairOracle : PairOracle where
  pairOk := pairOk
  pair_sound := fun D _ i j E h => pairOk_sound D i j E h

end CatalanCore.Uniform.Decay.PairEnergy
