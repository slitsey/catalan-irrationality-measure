import CatalanCore.Uniform.Decay.NearFast.Rep4
set_option Elab.async false

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

theorem fCm_close (n : ℕ) (a : ℕ → ℚ) (d : ℕ) (lv : ℚ) (DP : ℤ) (Dp : List ℤ) (DL0 DL1 : ℕ)
    (L0g L1g : GZ) (PA PB RR QN1p QN0p : List GZ) (QD1p QD0p : List ℤ) (PAQ PBQ : List GZ)
    (m : ℕ) (PAm PBm Rm JAm JBm L0c L1c : ℂ)
    (hDP : 0 < DP) (hDL0 : 0 < (DL0 : ℤ)) (hDL1 : 0 < (DL1 : ℤ))
    (hR : 0 < (fDw a d : ℤ) * ((d + 1).factorial : ℤ) * iget Dp d)
    (hJA : 0 < DP * ((n - 1).factorial : ℤ) * iget QD1p m)
    (hJB : 0 < DP * ((n - 1).factorial : ℤ) * iget QD0p m)
    (hP1 : (PAm * L1c).re = (((gget PA m).mul L1g).re : ℝ) / (((DP * DL1 : ℤ)) : ℝ))
    (hP2 : (PBm * L0c).re = (((gget PB m).mul L0g).re : ℝ) / (((DP * DL0 : ℤ)) : ℝ))
    (hP3 : Rm.re = -((gget RR m).re : ℝ) /
      ((((fDw a d : ℤ) * ((d + 1).factorial : ℤ) * iget Dp d : ℤ)) : ℝ))
    (hP4 : JAm.re = -(jetRe n PAQ QN1p m : ℝ) /
      (((DP * ((n - 1).factorial : ℤ) * iget QD1p m : ℤ)) : ℝ))
    (hP5 : JBm.re = -(jetRe n PBQ QN0p m : ℝ) /
      (((DP * ((n - 1).factorial : ℤ) * iget QD0p m : ℤ)) : ℝ)) :
    |((fCm n a d lv DP Dp DL0 DL1 L0g L1g PA PB RR QN1p QN0p QD1p QD0p PAQ PBQ m : ℤ) : ℝ) / (GG : ℝ)
      - ((PAm * L1c + PBm * L0c + Rm + JAm + JBm).re
        + (if m = 0 then (massQ a d : ℝ) * lv else 0))| ≤ 6 / (GG : ℝ) := by
  have f1 := fl_close ((gget PA m).mul L1g).re (DP * DL1) (by positivity)
  have f2 := fl_close ((gget PB m).mul L0g).re (DP * DL0) (by positivity)
  have f3 := fl_close (gget RR m).re _ hR
  have f4 := fl_close (jetRe n PAQ QN1p m) _ hJA
  have f5 := fl_close (jetRe n PBQ QN0p m) _ hJB
  have f6 := floor_close (massQ a d * lv)
  unfold fCm
  simp only [Complex.add_re, hP1, hP2, hP3, hP4, hP5]
  have hG := GG_posR
  have e1 : (6 : ℝ) / GG = 1 / GG + 1 / GG + 1 / GG + 1 / GG + 1 / GG + 1 / GG := by ring
  rw [e1]
  push_cast at f1 f2 f3 f4 f5
  have hGi : (0 : ℝ) < 1 / (GG : ℝ) := one_div_pos.2 hG
  have hsplit : ∀ A B C D E F G : ℝ, (A + B - C - D - E + F) / G = A / G + B / G - C / G - D / G - E / G + F / G := by
    intros; ring
  by_cases hm : m = 0
  · simp only [if_pos hm] 
    push_cast at f6 ⊢
    rw [hsplit]
    simp only [neg_div]
    rw [abs_le] at f1 f2 f3 f4 f5 f6 ⊢
    constructor <;> linarith [f1.1, f1.2, f2.1, f2.2, f3.1, f3.2, f4.1, f4.2, f5.1, f5.2, f6.1, f6.2]
  · simp only [if_neg hm]
    push_cast
    rw [hsplit]
    simp only [neg_div, zero_div, add_zero]
    rw [abs_le] at f1 f2 f3 f4 f5 ⊢
    constructor <;> linarith [f1.1, f1.2, f2.1, f2.2, f3.1, f3.2, f4.1, f4.2, f5.1, f5.2]

end CatalanCore.Uniform.Decay.NearFast
