import CatalanCore.Uniform.Bank.Sevenths.Rounding
import CatalanCore.Uniform.Bank.Sevenths.PoleData
import CatalanCore.Uniform.Content.Smith.LP1Table
import CatalanCore.Uniform.Content.Smith.LP2Entries
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Smith

theorem sevenths_lp1_size (r m p : ℕ) (hm : 12 * m < r + 6)
    (hcut : 7 * r ≤ 12 * p) : r + 2 * m ≤ 2 * p := by omega

theorem sevenths_lp2_size (o j r m p k : ℕ) (ho : 1 ≤ o)
    (hm : 12 * m < r + 6) (hk : 7 * k = j * p + o)
    (hcut : 49 * r ≤ 6 * (7 + j) * p) : r + 2 * m ≤ p + k := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at hcut
  omega

theorem sevenths_lp2_pole_le (o j r m p k : ℕ) (ho : o ≤ 6) (hj : j ≤ 6)
    (hp : 64 ≤ p) (hm : 12 * m < r + 6) (hk : 7 * k = j * p + o)
    (hupper : p < r + m) : k ≤ r := by
  have hjp := Nat.mul_le_mul_right p hj
  nlinarith

theorem sevenths_lp1_hyp (a : Fin 6) (p r m j : ℕ) [Fact p.Prime]
    (hp64 : 64 ≤ p) (hj : 1 ≤ j) (hroot : 7 * seventhRho a p = j * p + seventhOffset a)
    (hN : r + 2 * m ≤ 2 * p) (hrp : p ≤ r)
    (hUk : r < p + seventhRho a p) :
    LP1Hyp (seventhsFrameAt a) p 7 (7 - seventhNumerator a) r m (seventhRho a p) j := by
  have hb := seventhRho_bounds a p (by omega)
  have hpp : 64 * p ≤ p * p := Nat.mul_le_mul_right p hp64
  have hs := sevenths_simple_poles a p (r + 2 * m) (by nlinarith)
  have hn := sevenths_norm_good a p hp64
  exact ⟨⟨sevenths_twoTerm a, ⟨by omega, hroot, hb.1, hb.2, hj, hN⟩, hs, hn.1, hn.2⟩,
    hrp, hUk, by omega⟩

theorem sevenths_lp2_hyp (a : Fin 6) (p r m j : ℕ) [Fact p.Prime]
    (hp64 : 64 ≤ p) (hj : 1 ≤ j) (hroot : 7 * seventhRho a p = j * p + seventhOffset a)
    (hN : r + 2 * m ≤ p + seventhRho a p) (hrp : r < p) (hkr : seventhRho a p ≤ r) :
    LP2Hyp (seventhsFrameAt a) p 7 (7 - seventhNumerator a) r m (seventhRho a p) j := by
  have hb := seventhRho_bounds a p (by omega)
  have hN2 : r + 2 * m ≤ 2 * p := by omega
  have hpp : 64 * p ≤ p * p := Nat.mul_le_mul_right p hp64
  have hs := sevenths_simple_poles a p (r + 2 * m) (by nlinarith)
  have hn := sevenths_norm_good a p hp64
  exact ⟨⟨sevenths_twoTerm a, ⟨by omega, hroot, hb.1, hb.2, hj, hN⟩, hs, hn.1, hn.2⟩,
    hrp, hkr, by omega⟩

#print axioms sevenths_lp1_hyp
#print axioms sevenths_lp2_hyp
end CatalanCore.Uniform.Bank.Sevenths
