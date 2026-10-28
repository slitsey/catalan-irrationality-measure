import CatalanCore.Uniform.Decay.NearFast.Rep5
set_option Elab.async false

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

theorem jetRe_rep (n m : ℕ) (P : ℕ → CQ) (q : CQ) (PA : List GZ) (QN : GZ) (QNp : List GZ)
    (QD DP : ℤ) (QDp : List ℤ) (hn : m < n)
    (hP : ∀ j, j < m → (P j).toC * (DP : ℂ) = (gget PA j).toC)
    (hq : q.toC * (QD : ℂ) = QN.toC) (hQD : 0 < QD) (hDP : 0 < DP)
    (hQDp : ∀ j, j < n → iget QDp j = QD ^ j)
    (hQNp : ∀ i, i < n → (gget QNp i).toC = QN.toC ^ i) :
    (jetc P q m).toC.re = -(jetRe n ((List.range n).map fun j => (gget PA j).smul (iget QDp j)) QNp m : ℝ) /
      (((DP * ((n - 1).factorial : ℤ) * iget QDp m : ℤ)) : ℝ) := by
  have hQDc : (QD : ℂ) ≠ 0 := by exact_mod_cast hQD.ne'
  have hDPc : (DP : ℂ) ≠ 0 := by exact_mod_cast hDP.ne'
  have hF : ∀ j, j < m → (m - j) ∣ (n - 1).factorial := fun j hj =>
    Nat.dvd_factorial (by omega) (by omega)
  have hjet := jet_rep P q (fun j => gget PA j) QN QD DP (n - 1).factorial m hP hq hQDc hDPc hF
  have hpos : 0 < DP * ((n - 1).factorial : ℤ) * iget QDp m := by
    rw [hQDp m hn]
    have : 0 < ((n - 1).factorial : ℤ) := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hc := re_of_mul (jetc P q m).toC
    (-∑ j ∈ range m, ((((n - 1).factorial / (m - j) : ℕ)) : ℂ) *
      ((gget PA j).toC * (QD : ℂ) ^ j * QN.toC ^ (m - j)))
    (DP * ((n - 1).factorial : ℤ) * iget QDp m) (by
    rw [hQDp m hn]; push_cast; exact hjet) hpos.ne'
  rw [hc]
  congr 1
  unfold jetRe
  rw [cast_sumI, Complex.neg_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < m := Finset.mem_range.1 hj
  rw [gget_map_range _ n j (by omega)]
  rw [Int.cast_mul, GZ.mul_re_cast, GZ.toC_smul, hQNp (m - j) (by omega), hQDp j (by omega)]
  have h1 : ((((n - 1).factorial / (m - j) : ℕ)) : ℂ) = ((((n - 1).factorial / (m - j) : ℕ) : ℝ) : ℂ) := by
    simp
  rw [h1, Complex.re_ofReal_mul, Int.cast_natCast]
  simp only [Int.cast_pow]
  ring_nf

end CatalanCore.Uniform.Decay.NearFast
