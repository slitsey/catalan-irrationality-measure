module
public import CatalanMeasure.G728.Cert.YCells0
public import CatalanMeasure.G728.Cert.YCells1
public import CatalanMeasure.G728.Cert.YCells2
public import CatalanMeasure.G728.Cert.YCells3
public import CatalanMeasure.G728.Cert.YCells4
public import CatalanMeasure.G728.Cert.YCells5
public import CatalanMeasure.G728.Cert.YCells6
public import CatalanMeasure.G728.Cert.YCells7
public import CatalanMeasure.G728.Cert.YCells8
public import CatalanMeasure.G728.Cert.YCells9
public import CatalanMeasure.G728.Cert.YCells10
public import CatalanMeasure.G728.Cert.YCells11
public import CatalanMeasure.G728.Cert.YCells12
public import CatalanMeasure.G728.Cert.YCells13
public import CatalanMeasure.G728.Cert.YCells14
public import CatalanMeasure.G728.Cert.YCells15
public import CatalanMeasure.G728.Cert.YCells16
public import CatalanMeasure.G728.Cert.YCells17
public import CatalanMeasure.G728.Cert.YZ
public import CatalanMeasure.G728.Cert.YMG
public import CatalanMeasure.G728.CellSound
public import CatalanMeasure.G728.Glue
@[expose] public section
namespace CatalanMeasure.G728
open Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open CatalanMeasure.Cert
def cellsY : List TCell := (((((((((((((((((cellsY_0 ++ cellsY_1) ++ cellsY_2) ++ cellsY_3) ++ cellsY_4) ++ cellsY_5) ++ cellsY_6) ++ cellsY_7) ++ cellsY_8) ++ cellsY_9) ++ cellsY_10) ++ cellsY_11) ++ cellsY_12) ++ cellsY_13) ++ cellsY_14) ++ cellsY_15) ++ cellsY_16) ++ cellsY_17)
theorem cellsY_ok : ∀ c ∈ cellsY, cellT (colSpecS C Vc V) D_Y 5 65 MGL_Y MY c = true :=
  (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append cellsY_0_ok cellsY_1_ok) cellsY_2_ok) cellsY_3_ok) cellsY_4_ok) cellsY_5_ok) cellsY_6_ok) cellsY_7_ok) cellsY_8_ok) cellsY_9_ok) cellsY_10_ok) cellsY_11_ok) cellsY_12_ok) cellsY_13_ok) cellsY_14_ok) cellsY_15_ok) cellsY_16_ok) cellsY_17_ok)
theorem sound_Y (t : ℕ) : (colSpecS C Vc V t).Sound D_Y (colFieldS C Vc V) := colSpecS_sound C tailsV V_nonzero D_Y hZ_Y (by norm_num [C]) (by norm_num [C]) t
theorem peel_pt_Y (t : ℕ) (pr : ℚ × ℚ) (h : colPeel C t = some pr) : pr.2 = 0 ∨ pr.2 = 1 := by
  unfold colPeel at h
  split at h <;> first | (cases h; simp) | simp_all
theorem cover_Y : coverFrom 1 0 cellsY = true := by decide +kernel
theorem column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldS C Vc V s ≤ MY := by
  intro x hx
  have hxp : ∀ c ∈ cellsY, ∀ pr, (colSpecS C Vc V c.2.2).peel = some pr → x ≠ (pr.2 : ℝ) := by
    intro c _ pr h
    rcases peel_pt_Y c.2.2 pr h with h0 | h1
    · rw [h0]; simpa using hx.1.ne'
    · rw [h1]; simpa using hx.2.ne
  refine field_le_of_cells _ (colSpecS C Vc V) D_Y D_Y_ok 5 65 MGL_Y hMGL_Y MY cellsY
    (fun c _ => sound_Y c.2.2) 0 1 cover_Y cellsY_ok x ?_ ?_ hxp
  · simpa using hx.1.le
  · simpa using hx.2.le
end CatalanMeasure.G728
