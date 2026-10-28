module
public import CatalanMeasure.GenD.Uniform.W.Lucas.Cell
public import CatalanMeasure.GenD.Uniform.W.Lucas.DataA
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Theorem A cell: the J-affine equations over `ℚ`

Window `S = 35`, digits `J ∈ [4, 31]`, blocks `k0 = -2`, `K = 27`, moment tables `u < 40`, `J < 33`.
`PhiTm(J,34;y) - PhiTm(J,35;y)` is affine in `J` on the digit range.  One kernel declaration per
digit (a single declaration for all 28 digits exceeds 4.5 GB).
-/

namespace CatalanMeasure.GenD.Uniform.W.Lucas
open CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.MTGlue

def yA (k : ℕ) : ℤ := yzA.getD k 0

theorem yA_ne : yA 0 ≠ 0 := by
  show yzA.getD 0 0 ≠ 0
  decide +kernel

/-- The cell constants `D(4)`, `D(5)`. -/
def dA (J : ℕ) : ℚ :=
  Q.PhiQ (cmb yA (-2) 27 y2uI) (cmb yA (-2) 27 tI) J 34 -
    Q.PhiQ (cmb yA (-2) 27 y2uI) (cmb yA (-2) 27 tI) J 35

theorem dA_4 : dA 4 = dA 4 + (((4:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_5 : dA 5 = dA 4 + (((5:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_6 : dA 6 = dA 4 + (((6:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_7 : dA 7 = dA 4 + (((7:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_8 : dA 8 = dA 4 + (((8:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_9 : dA 9 = dA 4 + (((9:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_10 : dA 10 = dA 4 + (((10:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_11 : dA 11 = dA 4 + (((11:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_12 : dA 12 = dA 4 + (((12:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_13 : dA 13 = dA 4 + (((13:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_14 : dA 14 = dA 4 + (((14:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_15 : dA 15 = dA 4 + (((15:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_16 : dA 16 = dA 4 + (((16:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_17 : dA 17 = dA 4 + (((17:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_18 : dA 18 = dA 4 + (((18:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_19 : dA 19 = dA 4 + (((19:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_20 : dA 20 = dA 4 + (((20:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_21 : dA 21 = dA 4 + (((21:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_22 : dA 22 = dA 4 + (((22:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_23 : dA 23 = dA 4 + (((23:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_24 : dA 24 = dA 4 + (((24:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_25 : dA 25 = dA 4 + (((25:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_26 : dA 26 = dA 4 + (((26:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_27 : dA 27 = dA 4 + (((27:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_28 : dA 28 = dA 4 + (((28:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_29 : dA 29 = dA 4 + (((29:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_30 : dA 30 = dA 4 + (((30:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem dA_31 : dA 31 = dA 4 + (((31:ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  decide +kernel

theorem cellA_eq : ∀ J ∈ List.range' 4 28,
    dA J = dA 4 + (((J : ℤ) - 4 : ℤ) : ℚ) * (dA 5 - dA 4) := by
  intro J hJ
  rw [List.mem_range'_1] at hJ
  have : J = 4 ∨ J = 5 ∨ J = 6 ∨ J = 7 ∨ J = 8 ∨ J = 9 ∨ J = 10 ∨ J = 11 ∨ J = 12 ∨ J = 13 ∨ J = 14 ∨
    J = 15 ∨ J = 16 ∨ J = 17 ∨ J = 18 ∨ J = 19 ∨ J = 20 ∨ J = 21 ∨ J = 22 ∨ J = 23 ∨ J = 24 ∨
    J = 25 ∨ J = 26 ∨ J = 27 ∨ J = 28 ∨ J = 29 ∨ J = 30 ∨ J = 31 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dA_4
  · exact dA_5
  · exact dA_6
  · exact dA_7
  · exact dA_8
  · exact dA_9
  · exact dA_10
  · exact dA_11
  · exact dA_12
  · exact dA_13
  · exact dA_14
  · exact dA_15
  · exact dA_16
  · exact dA_17
  · exact dA_18
  · exact dA_19
  · exact dA_20
  · exact dA_21
  · exact dA_22
  · exact dA_23
  · exact dA_24
  · exact dA_25
  · exact dA_26
  · exact dA_27
  · exact dA_28
  · exact dA_29
  · exact dA_30
  · exact dA_31

/-- The Theorem A cell. -/
def cellA : ACell where
  Ub := 40
  Jb := 33
  S := 35
  Jlo := 4
  Jhi := 31
  K := 27
  k0 := -2
  y := yA
  ky := 0
  hS := by norm_num
  hJ := by norm_num
  hky := by norm_num

theorem cellA_affine : cellA.Affine := fun J hJ => cellA_eq J hJ

end CatalanMeasure.GenD.Uniform.W.Lucas
end
