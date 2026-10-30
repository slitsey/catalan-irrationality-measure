import CatalanCore.Uniform.Bank.Fifths.Frame
import CatalanFrames.Thirds.Frame
import CatalanCore.Uniform.Content.Smith.TwoTerm
set_option Elab.async false

/-! # Two-term data of the fifths frames (lane B, B5c)

`fifthsFrame s ...` (norm 25) is `Thirds.thirdsFrame s 25 ...`.  For the shift `s = (q - o)/q` the
frame has increments `Δ_t = 1/t - q/(q t - o)`, `D_t = 1/t² - q²/(q t - o)²` (`TwoTermData Fr q o`);
for the fifths frames `q = 5`, `o = 5 - a` (`o = 4, 3, 2, 1`). -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Bank.Fifths

theorem fifthsFrame_eq_thirds (s xs δ0 : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1) :
    fifthsFrame s xs δ0 n0off hs0 hs1 =
      CatalanFrames.Thirds.thirdsFrame s 25 xs δ0 n0off hs0 hs1 (by norm_num) := rfl

theorem thirdsFrame_twoTerm (q o : ℕ) (ho : 0 < o) (hoq : o < q) (s N xs δ0 : ℚ) (n0 : ℕ)
    (h0 : 0 < s) (h1 : s < 1) (hN : 0 < N) (hs : s = ((q : ℚ) - o) / q) :
    TwoTermData (CatalanFrames.Thirds.thirdsFrame s N xs δ0 n0 h0 h1 hN) q o where
  o_pos := ho
  o_lt := hoq
  delta_eq t ht := by
    have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have e : (t : ℚ) - 1 + s = ((q : ℚ) * t - o) / q := by rw [hs]; field_simp; ring
    rw [CatalanFrames.Thirds.Delta_eq, e, one_div_div]
  dsq_eq t ht := by
    have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have e : (t : ℚ) - 1 + s = ((q : ℚ) * t - o) / q := by rw [hs]; field_simp; ring
    rw [CatalanFrames.Thirds.Dsq_eq, e, div_pow, one_div_div]

theorem fifths1_twoTerm : TwoTermData fifths1 5 4 :=
  thirdsFrame_twoTerm 5 4 (by norm_num) (by norm_num) _ _ _ _ _ _ _ _ (by norm_num)
theorem fifths2_twoTerm : TwoTermData fifths2 5 3 :=
  thirdsFrame_twoTerm 5 3 (by norm_num) (by norm_num) _ _ _ _ _ _ _ _ (by norm_num)
theorem fifths3_twoTerm : TwoTermData fifths3 5 2 :=
  thirdsFrame_twoTerm 5 2 (by norm_num) (by norm_num) _ _ _ _ _ _ _ _ (by norm_num)
theorem fifths4_twoTerm : TwoTermData fifths4 5 1 :=
  thirdsFrame_twoTerm 5 1 (by norm_num) (by norm_num) _ _ _ _ _ _ _ _ (by norm_num)

#print axioms fifths1_twoTerm
#print axioms fifths4_twoTerm
end CatalanCore.Uniform.Bank.FifthsContent
