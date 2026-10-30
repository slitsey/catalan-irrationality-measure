module

public import CatalanCore.Uniform.Bank.ThirdsContent.OfBounds
public import CatalanFrames.Thirds.Instance
public import CatalanFrames.Thirds.ContourInstances
public import CatalanCore.Uniform.Content.Smith.TwoTerm

@[expose] public section
set_option Elab.async false

/-! # Two-term data of the thirds frames (lane B, B4b)

A `ThirdsData Fr e` (`Φ(k) = k(3k - e)`, norm 9) gives `TwoTermData Fr 3 e`
(`Δ_t = 1/t - 3/(3t - e)`, `D_t = 1/t² - 9/(3t - e)²`): `e = 2` for `thirdsAc`, `e = 1` for `thirdsBc`. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform.Content.Smith CatalanFrames.Thirds

theorem ThirdsData.twoTerm {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) : TwoTermData Fr 3 e where
  o_pos := by rcases T.he with h | h <;> omega
  o_lt := by rcases T.he with h | h <;> omega
  delta_eq t ht := by
    rw [T.delta t ht, cast3 T.he ht]
    push_cast; ring
  dsq_eq t ht := by
    rw [T.dsq t ht, cast3 T.he ht]
    push_cast; ring

theorem thirdsAc_data : ThirdsData thirdsAc 2 :=
  ThirdsData.of_thirdsFrame (Or.inr rfl) (1 / 3) (by norm_num) (2 / 3) (1 / 3) 1
    (by norm_num) (by norm_num) (by norm_num)

theorem thirdsBc_data : ThirdsData thirdsBc 1 :=
  ThirdsData.of_thirdsFrame (Or.inl rfl) (2 / 3) (by norm_num) (1 / 3) (1 / 3) 0
    (by norm_num) (by norm_num) (by norm_num)

theorem thirdsAc_twoTerm : TwoTermData thirdsAc 3 2 := ThirdsData.twoTerm thirdsAc_data
theorem thirdsBc_twoTerm : TwoTermData thirdsBc 3 1 := ThirdsData.twoTerm thirdsBc_data

end CatalanCore.Uniform.Bank.ThirdsContent
