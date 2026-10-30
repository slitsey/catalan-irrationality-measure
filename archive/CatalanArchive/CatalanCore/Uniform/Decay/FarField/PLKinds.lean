import CatalanCore.Uniform.Decay.FarField.LinJet
import CatalanCore.Uniform.Decay.FarField.CapPL
import CatalanCore.Uniform.Decay.PolyWire2.Top2
set_option Elab.async false

/-!
# PL cap cells as a cell kind (lane D, package D15)

`PLCap` is a PL cap cell `(a, b, ua, ub)` with a kind:
* `const k` : an existing constant upper-bound cell `k : TCell2 × ℚ` of `PolyWire2` (so a table of
  `capC` converts cell by cell, `ua = ub = k.2`), checked by `ubCellOk2`;
* `lin n lo C Fs` : the chord from `ua` to `ub` is a majorant of `g`, certified by the jet rule with a
  linear shift (`cellOkFL`) applied to the negated pieces.

`plUbOk` is the Boolean and `plUbOk_sound` gives `g ≤ plLine` on the cell.  Together with
`CapPL.plCapOkOf_sound` this is a drop-in replacement for the `ubCellOk2` oracle of the cap.
-/

namespace CatalanCore.Uniform.Decay.FarField

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2

inductive PLKind where
  | const (k : TCell2 × ℚ)
  | lin (n : ℕ) (lo : ℚ) (C : List ℚ) (Fs : ℚ)

structure PLCap where
  cell : PLCell
  kind : PLKind

/-- The Boolean of one PL cap cell (upper bound of `g` by the chord). -/
def plUbOk (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (x : PLCap) : Bool :=
  match x.kind with
  | .const k =>
      decide (x.cell = (k.1.ulo, k.1.uhi, k.2, k.2)) && ubCellOk2 nu Rtwo eW eP D k
  | .lin n lo C Fs =>
      decide (D.ε < 1) && decide (0 ≤ D.W) && decide (x.cell.1 < x.cell.2.1) &&
        cellOkFL n ((cellPieces D nu).map negW) ⟨(x.cell.1 + x.cell.2.1) / 2, 0⟩ ⟨1, 0⟩
          ((x.cell.2.1 - x.cell.1) / 2) D.W Rtwo 0 lo 0 C Fs eW eP
          ((x.cell.2.2.1 + x.cell.2.2.2) / 2)
          ((x.cell.2.2.2 - x.cell.2.2.1) / (x.cell.2.1 - x.cell.1))

theorem plUbOk_sound (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (x : PLCap)
    (h : plUbOk nu Rtwo eW eP D x = true) :
    ∀ y : ℝ, (x.cell.1 : ℝ) ≤ y → y ≤ x.cell.2.1 →
      gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨y, 0⟩ ≤ plLine x.cell y := by
  intro y hy1 hy2
  unfold plUbOk at h
  rcases x with ⟨⟨a, b, ua, ub⟩, k⟩
  cases k with
  | const k =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hcell, hok⟩ := h
    simp only [Prod.mk.injEq] at hcell
    obtain ⟨h1, h2, h3, h4⟩ := hcell
    have := ubCellOk2_sound nu Rtwo eW eP hV D k hok y (by simp only at hy1; rw [← h1]; exact hy1)
      (by simp only at hy2; rw [← h2]; exact hy2)
    unfold plLine
    simp only
    subst h3; subst h4
    simpa using this
  | lin n lo C Fs =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hε, hW⟩, hab⟩, hc⟩ := h
    simp only at hy1 hy2 hab hc
    have hWR : (0 : ℝ) ≤ D.W := by exact_mod_cast hW
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    have key := cellOkFL_sound hc (y - (((a + b) / 2 : ℚ) : ℝ)) 0 (by
      rw [abs_le]; push_cast; constructor <;> linarith) (by simpa using hWR)
    have hz : (⟨((a + b) / 2 : ℚ), 0⟩ : CQ).toC + ((y - (((a + b) / 2 : ℚ) : ℝ) : ℝ) : ℂ) *
        (⟨1, 0⟩ : CQ).toC + ((0 : ℝ) : ℂ) = ⟨y, 0⟩ := by
      apply Complex.ext <;> simp [CQ.toC]
    rw [hz, negW_sum] at key
    rw [gNu_eq D nu hV]
    have him : (⟨y, 0⟩ : ℂ).im = 0 := rfl
    rw [him] at key ⊢
    simp only [abs_zero, mul_zero, add_zero, Rat.cast_zero, zero_mul, zero_add] at key ⊢
    unfold plLine
    simp only
    have hba : (b : ℝ) - a ≠ 0 := by linarith
    have e : (((ua + ub) / 2 : ℚ) : ℝ) + (((ub - ua) / (b - a) : ℚ) : ℝ) * (y - (((a + b) / 2 : ℚ) : ℝ))
        = (ua : ℝ) + ((ub : ℝ) - ua) * (y - a) / ((b : ℝ) - a) := by
      push_cast
      field_simp
      ring
    rw [e] at key
    linarith

/-- A constant upper-bound cell of `PolyWire2` as a PL cell. -/
def PLCap.ofConst (k : TCell2 × ℚ) : PLCap := ⟨(k.1.ulo, k.1.uhi, k.2, k.2), .const k⟩

theorem plUbOk_ofConst (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (k : TCell2 × ℚ)
    (h : ubCellOk2 nu Rtwo eW eP D k = true) :
    plUbOk nu Rtwo eW eP D (PLCap.ofConst k) = true := by
  simp [plUbOk, PLCap.ofConst, h]

end CatalanCore.Uniform.Decay.FarField
