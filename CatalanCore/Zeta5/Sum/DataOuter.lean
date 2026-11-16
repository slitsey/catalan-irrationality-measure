module

public import CatalanCore.Zeta5.Sum.Seg

@[expose] public section

/-!
# Data: the outer integral (ZC34) and the outer saving (ZC35)

Cut lists generated from the closed formula (breakpoints `n/c` and guard roots); every cell is
checked by the decidable test `cellOKE` / `cellOKH`, values by `Profile.chain`.
-/

open Set MeasureTheory

namespace CatalanCore.Zeta5.Sum

open CatalanCore.Zeta5.Profile

set_option maxRecDepth 100000

theorem e01 : segE (20 / 37 : ℚ) [(40 / 43 : ℚ), (1 : ℚ), (40 / 37 : ℚ), (3 / 2 : ℚ), (20 / 13 : ℚ), (60 / 37 : ℚ), (80 / 43 : ℚ), (2 : ℚ), (80 / 37 : ℚ), (30 / 13 : ℚ), (5 / 2 : ℚ), (100 / 37 : ℚ), (120 / 43 : ℚ), (3 : ℚ)] (127751 / 96000 : ℚ) (3 : ℚ) = true := by
  -- kcost: 3 s measured (16 Nov dev compile, one chunk of at most 100 cells)
  decide +kernel


/-- **ZC34** (x-coordinates, `x = 1/y`): `∫_{20/37}^3 (x T₀(1/x)) x⁻³ dx = 127751/96000`;
14 affine pieces. -/
theorem zc34_x : ∫ x in (20 / 37 : ℝ)..3, Ex x / x ^ 3 = 127751 / 96000 := by
  have h := segE_sound e01
  have e : ((127751 / 96000 : ℚ) : ℚ) = 127751 / 96000 := by
    -- kcost: 1 s estimated (a few rational additions)
    decide +kernel
  have := h.2.2
  rw [e] at this
  norm_num at this
  exact this

theorem h01 : segH (1 : ℚ) [(40 / 37 : ℚ), (30 / 23 : ℚ), (3 / 2 : ℚ), (20 / 13 : ℚ), (60 / 37 : ℚ), (40 / 23 : ℚ), (80 / 43 : ℚ), (2 : ℚ), (80 / 37 : ℚ), (50 / 23 : ℚ), (30 / 13 : ℚ), (170 / 69 : ℚ), (5 / 2 : ℚ), (60 / 23 : ℚ), (100 / 37 : ℚ), (120 / 43 : ℚ), (3 : ℚ)] (3203 / 163200 : ℚ) (3 : ℚ) = true := by
  -- kcost: 3 s measured (16 Nov dev compile, one chunk of at most 100 cells)
  decide +kernel

/-- **ZC35** (x-coordinates): `∫_1^3 [x T₀(1/x) − R(x)]₊ x⁻³ dx = 3203/163200`; 17 cells, 5 of
them with positive saving. -/
theorem zc35_x : ∫ x in (1 : ℝ)..3, max 0 (Ex x - Rg x) / x ^ 3 = 3203 / 163200 := by
  have h := segH_sound h01
  have e : ((3203 / 163200 : ℚ) : ℚ) = 3203 / 163200 := by
    -- kcost: 1 s estimated (a few rational additions)
    decide +kernel
  have := h.2.2
  rw [e] at this
  norm_num at this
  exact this

end CatalanCore.Zeta5.Sum
