import CatalanCore.Uniform.Decay.NearFast.Rep3
set_option Elab.async false

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

theorem GG_pos : (0 : ℤ) < GG := by unfold GG; norm_num

theorem GG_posR : (0 : ℝ) < (GG : ℝ) := by exact_mod_cast GG_pos

theorem grid_close (q v G : ℝ) (hG : 0 < G) (h1 : q ≤ v * G) (h2 : v * G < q + 1) :
    |q / G - v| ≤ 1 / G := by
  have e1 : q / G ≤ v := (div_le_iff₀ hG).2 h1
  have e2 : v ≤ q / G + 1 / G := by
    rw [← add_div, le_div_iff₀ hG]; linarith
  rw [abs_le]; constructor <;> linarith

theorem fl_close (x den : ℤ) (hd : 0 < den) :
    |((fl x den : ℤ) : ℝ) / (GG : ℝ) - (x : ℝ) / (den : ℝ)| ≤ 1 / (GG : ℝ) := by
  unfold fl
  have h1 := Int.ediv_mul_le (x * GG) hd.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (x * GG) hd
  have hdR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hd
  have hG := GG_posR
  set q := x * GG / den with hq
  have h1R : (q : ℝ) * den ≤ x * GG := by exact_mod_cast h1
  have h2R : (x : ℝ) * GG < (q + 1) * den := by exact_mod_cast h2
  refine grid_close _ _ _ hG ?_ ?_
  · rw [div_mul_eq_mul_div, le_div_iff₀ hdR]; linarith
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hdR]; linarith

theorem floor_close (y : ℚ) :
    |((⌊y * (GG : ℚ)⌋ : ℤ) : ℝ) / (GG : ℝ) - (y : ℝ)| ≤ 1 / (GG : ℝ) := by
  have hG := GG_posR
  have h1 : ((⌊y * (GG : ℚ)⌋ : ℤ) : ℚ) ≤ y * GG := Int.floor_le _
  have h2 : y * (GG : ℚ) < ((⌊y * (GG : ℚ)⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
  have h1R : ((⌊y * (GG : ℚ)⌋ : ℤ) : ℝ) ≤ (y : ℝ) * GG := by exact_mod_cast h1
  have h2R : (y : ℝ) * GG < ((⌊y * (GG : ℚ)⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast h2
  exact grid_close _ _ _ hG h1R h2R

theorem re_of_mul (z w : ℂ) (c : ℤ) (h : z * (c : ℂ) = w) (hc : c ≠ 0) :
    z.re = w.re / (c : ℝ) := by
  have h' := congrArg Complex.re h
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  rw [Complex.mul_re] at h'
  simp at h'
  rw [eq_div_iff hcR]; exact h'

theorem getD_map_range (f : ℕ → ℤ) (n m : ℕ) (h : m < n) :
    ((List.range n).map f).getD m 0 = f m := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]

theorem pieceCoef_cast (n : ℕ) (P : WP) (z0 e L0 L1 : CQ) (lv : ℚ) (m : ℕ) :
    ((pieceCoef n P z0 e L0 L1 lv m : ℚ) : ℝ) =
      ((PAc (coeffs P.a) (P.a.length - 1) z0 e m).toC * L1.toC
        + (PBc (coeffs P.a) (P.a.length - 1) z0 e m).toC * L0.toC
        + (Rc (coeffs P.a) (P.a.length - 1) z0 e m).toC
        + (jetc (PAc (coeffs P.a) (P.a.length - 1) z0 e) (q1of z0 e) m).toC
        + (jetc (PBc (coeffs P.a) (P.a.length - 1) z0 e) (q0of z0 e) m).toC).re
      + (if m = 0 then (massQ (coeffs P.a) (P.a.length - 1) : ℝ) * lv else 0) := by
  unfold pieceCoef
  push_cast
  congr 1
  · rw [← CQ.toC_re]
    simp only [CQ.toC_add, CQ.toC_mul]
  · split_ifs <;> simp

end CatalanCore.Uniform.Decay.NearFast
