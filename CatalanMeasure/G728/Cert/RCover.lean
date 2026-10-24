module
public import CatalanMeasure.G728.Cert.RCells0
public import CatalanMeasure.G728.Cert.RCells1
public import CatalanMeasure.G728.Cert.RCells2
public import CatalanMeasure.G728.Cert.RCells3
public import CatalanMeasure.G728.Cert.RCells4
public import CatalanMeasure.G728.Cert.RCells5
public import CatalanMeasure.G728.Cert.RCells6
public import CatalanMeasure.G728.Cert.RCells7
public import CatalanMeasure.G728.Cert.RCells8
public import CatalanMeasure.G728.Cert.RCells9
public import CatalanMeasure.G728.Cert.RCells10
public import CatalanMeasure.G728.Cert.RCells11
public import CatalanMeasure.G728.Cert.RCells12
public import CatalanMeasure.G728.Cert.RCells13
public import CatalanMeasure.G728.Cert.RCells14
public import CatalanMeasure.G728.Cert.RZ
public import CatalanMeasure.G728.Cert.RMG
public import CatalanMeasure.G728.CellSound
public import CatalanMeasure.G728.Facts
@[expose] public section
namespace CatalanMeasure.G728
open Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open CatalanMeasure.Cert
def cellsR : List TCell := ((((((((((((((cellsR_0 ++ cellsR_1) ++ cellsR_2) ++ cellsR_3) ++ cellsR_4) ++ cellsR_5) ++ cellsR_6) ++ cellsR_7) ++ cellsR_8) ++ cellsR_9) ++ cellsR_10) ++ cellsR_11) ++ cellsR_12) ++ cellsR_13) ++ cellsR_14)
theorem cellsR_ok : ∀ c ∈ cellsR, cellT (resSpecS Pc P) D_R 5 65 MGL_R MR c = true :=
  (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append cellsR_0_ok cellsR_1_ok) cellsR_2_ok) cellsR_3_ok) cellsR_4_ok) cellsR_5_ok) cellsR_6_ok) cellsR_7_ok) cellsR_8_ok) cellsR_9_ok) cellsR_10_ok) cellsR_11_ok) cellsR_12_ok) cellsR_13_ok) cellsR_14_ok)
theorem sound_R (t : ℕ) : (resSpecS Pc P t).Sound D_R (resFieldS Pc P) := resSpecS_sound tailsP P_nonzero D_R hZ_R t
theorem TT_real_R : ((TT : ℤ) : ℝ) = 1099511627776 := by unfold TT; norm_num
theorem cover_R1 : coverFrom (-401/2500) (-1099511627776) (cellsR.take 189) = true := by decide +kernel
theorem cover_R2 : coverFrom 1 (qfloor ((401/2500 : ℚ) * (TT : ℚ))) (cellsR.drop 189) = true := by decide +kernel
theorem residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| → resFieldS Pc P x ≤ MR := by
  intro x hx hg
  have hxp : ∀ c ∈ cellsR, ∀ pr, (resSpecS Pc P c.2.2).peel = some pr → x ≠ (pr.2 : ℝ) := by
    intro c _ pr h
    simp [resSpecS] at h
  rcases le_abs'.mp hg with h | h
  · refine field_le_of_cells _ (resSpecS Pc P) D_R D_R_ok 5 65 MGL_R hMGL_R MR (cellsR.take 189)
      (fun c _ => sound_R c.2.2) (-1099511627776) (-401/2500) cover_R1
      (fun c hc => cellsR_ok c (List.mem_of_mem_take hc)) x ?_ ?_
      (fun c hc => hxp c (List.mem_of_mem_take hc))
    · rw [TT_real_R]; push_cast; rw [div_le_iff₀ (by norm_num)]; linarith [hx.1]
    · push_cast; linarith
  · refine field_le_of_cells _ (resSpecS Pc P) D_R D_R_ok 5 65 MGL_R hMGL_R MR (cellsR.drop 189)
      (fun c _ => sound_R c.2.2) (qfloor ((401/2500 : ℚ) * (TT : ℚ))) 1 cover_R2
      (fun c hc => cellsR_ok c (List.mem_of_mem_drop hc)) x
      (floor_le_of_ge (401/2500) x (by push_cast; linarith)) ?_
      (fun c hc => hxp c (List.mem_of_mem_drop hc))
    · simpa using hx.2
end CatalanMeasure.G728
