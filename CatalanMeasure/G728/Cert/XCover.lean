module
public import CatalanMeasure.G728.Cert.XCells0
public import CatalanMeasure.G728.Cert.XCells1
public import CatalanMeasure.G728.Cert.XCells2
public import CatalanMeasure.G728.Cert.XCells3
public import CatalanMeasure.G728.Cert.XCells4
public import CatalanMeasure.G728.Cert.XCells5
public import CatalanMeasure.G728.Cert.XCells6
public import CatalanMeasure.G728.Cert.XCells7
public import CatalanMeasure.G728.Cert.XCells8
public import CatalanMeasure.G728.Cert.XCells9
public import CatalanMeasure.G728.Cert.XCells10
public import CatalanMeasure.G728.Cert.XCells11
public import CatalanMeasure.G728.Cert.XCells12
public import CatalanMeasure.G728.Cert.XCells13
public import CatalanMeasure.G728.Cert.XCells14
public import CatalanMeasure.G728.Cert.XCells15
public import CatalanMeasure.G728.Cert.XCells16
public import CatalanMeasure.G728.Cert.XCells17
public import CatalanMeasure.G728.Cert.XCells18
public import CatalanMeasure.G728.Cert.XCells19
public import CatalanMeasure.G728.Cert.XCells20
public import CatalanMeasure.G728.Cert.XCells21
public import CatalanMeasure.G728.Cert.XCells22
public import CatalanMeasure.G728.Cert.XCells23
public import CatalanMeasure.G728.Cert.XZ
public import CatalanMeasure.G728.Cert.XMG
public import CatalanMeasure.G728.CellSound
public import CatalanMeasure.G728.Facts
@[expose] public section
namespace CatalanMeasure.G728
open Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open CatalanMeasure.Cert
def cellsX : List TCell := (((((((((((((((((((((((cellsX_0 ++ cellsX_1) ++ cellsX_2) ++ cellsX_3) ++ cellsX_4) ++ cellsX_5) ++ cellsX_6) ++ cellsX_7) ++ cellsX_8) ++ cellsX_9) ++ cellsX_10) ++ cellsX_11) ++ cellsX_12) ++ cellsX_13) ++ cellsX_14) ++ cellsX_15) ++ cellsX_16) ++ cellsX_17) ++ cellsX_18) ++ cellsX_19) ++ cellsX_20) ++ cellsX_21) ++ cellsX_22) ++ cellsX_23)
theorem cellsX_ok : ∀ c ∈ cellsX, cellT (rowSpecS R Pc Vc P V) D_X 5 65 MGL_X MX c = true :=
  (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append cellsX_0_ok cellsX_1_ok) cellsX_2_ok) cellsX_3_ok) cellsX_4_ok) cellsX_5_ok) cellsX_6_ok) cellsX_7_ok) cellsX_8_ok) cellsX_9_ok) cellsX_10_ok) cellsX_11_ok) cellsX_12_ok) cellsX_13_ok) cellsX_14_ok) cellsX_15_ok) cellsX_16_ok) cellsX_17_ok) cellsX_18_ok) cellsX_19_ok) cellsX_20_ok) cellsX_21_ok) cellsX_22_ok) cellsX_23_ok)
theorem sound_X (t : ℕ) : (rowSpecS R Pc Vc P V t).Sound D_X (rowFieldS R Pc Vc P V) := rowSpecS_sound R tailsP tailsV P_nonzero V_nonzero D_X hZ_X (by norm_num [R]) (by norm_num [R]) t
theorem TT_real_X : ((TT : ℤ) : ℝ) = 1099511627776 := by unfold TT; norm_num
theorem peel_pt_X (t : ℕ) (pr : ℚ × ℚ) (h : rowPeel R t = some pr) : pr.2 = 0 ∨ pr.2 = 1 := by
  unfold rowPeel at h
  split at h <;> first | (cases h; simp) | simp_all
theorem cover_X_neg : coverFrom 0 (-1099511627776) cellsX = true := by decide +kernel
theorem cover_X_pos : coverFrom 1 0 cellsX = true := by decide +kernel
theorem row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldS R Pc Vc P V x ≤ MX := by
  intro x hx
  have hx01 : x ≠ 0 ∧ x ≠ 1 := by
    rcases hx with hx | hx
    · exact ⟨hx.2.ne, by linarith [hx.2]⟩
    · exact ⟨hx.1.ne', hx.2.ne⟩
  have hxp : ∀ c ∈ cellsX, ∀ pr, (rowSpecS R Pc Vc P V c.2.2).peel = some pr → x ≠ (pr.2 : ℝ) := by
    intro c _ pr h
    rcases peel_pt_X c.2.2 pr h with h0 | h1
    · rw [h0]; simpa using hx01.1
    · rw [h1]; simpa using hx01.2
  rcases hx with hx | hx
  · refine field_le_of_cells _ (rowSpecS R Pc Vc P V) D_X D_X_ok 5 65 MGL_X hMGL_X MX cellsX
      (fun c _ => sound_X c.2.2) (-1099511627776) 0 cover_X_neg cellsX_ok x ?_ ?_ hxp
    · rw [TT_real_X]; push_cast; rw [div_le_iff₀ (by norm_num)]; linarith [hx.1]
    · simpa using hx.2.le
  · refine field_le_of_cells _ (rowSpecS R Pc Vc P V) D_X D_X_ok 5 65 MGL_X hMGL_X MX cellsX
      (fun c _ => sound_X c.2.2) 0 1 cover_X_pos cellsX_ok x ?_ ?_ hxp
    · simpa using hx.1.le
    · simpa using hx.2.le
end CatalanMeasure.G728
