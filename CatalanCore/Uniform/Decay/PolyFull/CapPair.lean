import CatalanCore.Uniform.Decay.PolyFull.Oracle2
import CatalanCore.Uniform.Decay.PolyCells.Assemble
set_option Elab.async false

/-!
# Cap integrals as pair energies (lane D, package D10)

The cap `[-r0, 0]` is the segment `capSegOf r0` (density one).  For any segment `s` with rational
density,
`W s z = ∫₀¹ f_s(t) (-log ‖z - p_s(t)‖) dt` is its potential at `z`, and
`pairBound (capSegOf r0) s = some u` gives `∫₀¹ W s (cap s') ds' ≤ u`.  Negating the density of `s`
turns the upper bound into a lower bound.  `listUb` adds up optional bounds over a list.
-/

namespace CatalanCore.Uniform.Decay.PolyFull

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.PairEnergy

/-- The cap segment `[-r0, 0]` with density one. -/
def capSegOf (r0 : ℚ) : Seg :=
  { ax := -r0, ay := 0, bx := 0, byy := 0, coef := [1], M := 1, Lq := r0, tau := 0 }

/-- A segment with the density negated. -/
def negSeg (s : Seg) : Seg := { s with coef := s.coef.map fun c => -c }

/-- The potential of a segment at `z`. -/
noncomputable def Wseg (s : Seg) (z : ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, evalL s.coef t *
    (-Real.log ‖z - ((segA s).toC + (t : ℂ) * ((segB s).toC - (segA s).toC))‖)

theorem evalL_neg (l : List ℚ) (t : ℝ) : evalL (l.map fun c => -c) t = -evalL l t := by
  induction l with
  | nil => simp [evalL]
  | cons c l ih => simp only [List.map_cons, evalL, ih]; push_cast; ring

theorem Wseg_neg (s : Seg) (z : ℂ) : Wseg (negSeg s) z = -Wseg s z := by
  unfold Wseg
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [negSeg, segA, segB, evalL_neg]
  ring

theorem segU_eq_Wseg (D : SplineData) (j : Fin D.n) (z : ℂ) : segU D j z = Wseg (D.seg j) z := by
  unfold segU Wseg
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [SplineData.f, SplineData.l, ratPoly_eq_evalL, pt, SplineData.A, SplineData.B,
    segA, segB, QC.toC]

/-- The cap point of parameter `s`. -/
noncomputable def capX (r0 : ℚ) (s : ℝ) : ℝ := (r0 : ℝ) * s + -(r0 : ℝ)

theorem capPt_eq (r0 : ℚ) (s : ℝ) :
    (segA (capSegOf r0)).toC + (s : ℂ) * ((segB (capSegOf r0)).toC - (segA (capSegOf r0)).toC) =
      ((capX r0 s : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [segA, segB, capSegOf, QC.toC, capX] <;> ring

/-- A pair bound, or `none`. -/
def pairBound (s1 s2 : Seg) : Option ℚ :=
  if (mkPair s1 s2).rel = QC.zero ∧ QC.sub (mkPair s1 s2).B1 (mkPair s1 s2).A1 ≠ QC.zero ∧
      QC.sub (mkPair s1 s2).B2 (mkPair s1 s2).A2 ≠ QC.zero then pairUb (mkPair s1 s2) else none

theorem pairBound_sound {s1 s2 : Seg} {u : ℚ} (h : pairBound s1 s2 = some u) :
    ∫ s in (0 : ℝ)..1, evalL s1.coef s * ∫ t in (0 : ℝ)..1, evalL s2.coef t *
      (-Real.log ‖((segA s1).toC + (s : ℂ) * ((segB s1).toC - (segA s1).toC)) -
        ((segA s2).toC + (t : ℂ) * ((segB s2).toC - (segA s2).toC))‖) ≤ (u : ℝ) := by
  apply pairCheck_sound
  unfold pairBound at h
  split_ifs at h with hc
  obtain ⟨h1, h2, h3⟩ := hc
  unfold pairCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [h]
  simp

theorem evalL_one (s : ℝ) : evalL [1] s = 1 := by simp [evalL]

/-- Bound of the cap integral of the potential of `s`. -/
theorem cap_pair_le {r0 : ℚ} {s : Seg} {u : ℚ} (h : pairBound (capSegOf r0) s = some u) :
    ∫ x in (0 : ℝ)..1, Wseg s ((capX r0 x : ℝ) : ℂ) ≤ (u : ℝ) := by
  have := pairBound_sound h
  have e : ∀ x : ℝ, evalL (capSegOf r0).coef x * ∫ t in (0 : ℝ)..1, evalL s.coef t *
      (-Real.log ‖((segA (capSegOf r0)).toC + (x : ℂ) * ((segB (capSegOf r0)).toC -
        (segA (capSegOf r0)).toC)) - ((segA s).toC + (t : ℂ) * ((segB s).toC - (segA s).toC))‖)
      = Wseg s ((capX r0 x : ℝ) : ℂ) := by
    intro x
    rw [capPt_eq]
    simp only [capSegOf, evalL_one, one_mul, Wseg]
  simp_rw [e] at this
  exact this

/-- Lower bound of the cap integral of the potential of `s`. -/
theorem cap_pair_ge {r0 : ℚ} {s : Seg} {u : ℚ} (h : pairBound (capSegOf r0) (negSeg s) = some u) :
    -(u : ℝ) ≤ ∫ x in (0 : ℝ)..1, Wseg s ((capX r0 x : ℝ) : ℂ) := by
  have := cap_pair_le h
  simp_rw [Wseg_neg] at this
  rw [intervalIntegral.integral_neg] at this
  linarith

/-- Sum of optional bounds over a list. -/
def listUb {α : Type} (f : α → Option ℚ) : List α → Option ℚ
  | [] => some 0
  | a :: l =>
    match f a, listUb f l with
    | some x, some y => some (x + y)
    | _, _ => none

theorem listUb_sound {α : Type} {f : α → Option ℚ} {F : α → ℝ}
    (hf : ∀ a u, f a = some u → F a ≤ (u : ℝ)) :
    ∀ (l : List α) {u : ℚ}, listUb f l = some u → (l.map F).sum ≤ (u : ℝ) := by
  intro l
  induction l with
  | nil => intro u h; simp [listUb] at h; subst h; simp
  | cons a l ih =>
    intro u h
    simp only [listUb] at h
    split at h
    · rename_i x y hx hy
      simp only [Option.some.injEq] at h; subst h
      simp only [List.map_cons, List.sum_cons]
      push_cast
      linarith [hf a x hx, ih hy]
    · simp at h

end CatalanCore.Uniform.Decay.PolyFull
