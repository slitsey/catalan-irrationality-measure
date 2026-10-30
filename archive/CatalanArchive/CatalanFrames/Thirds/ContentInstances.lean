module

public import CatalanFrames.Thirds.MinorContent
public import CatalanFrames.Thirds.ContourInstances

@[expose] public section

/-!
# Thin instances: content of `thirdsAc` (`s = 1/3`, `e = 2`) and `thirdsBc` (`s = 2/3`, `e = 1`)

The frames are those of `ContourInstances` (norm `9`).  Class `1 (mod 6)` is the low class for
`thirdsAc` and the high class for `thirdsBc`.
-/

open CatalanCore CatalanCore.Rect

namespace CatalanFrames.Thirds

theorem thirdsAc_data : ThirdsData thirdsAc 2 :=
  ThirdsData.of_thirdsFrame (Or.inr rfl) (1 / 3) (by norm_num) (2 / 3) (1 / 3) 1
    (by norm_num) (by norm_num) (by norm_num)

theorem thirdsBc_data : ThirdsData thirdsBc 1 :=
  ThirdsData.of_thirdsFrame (Or.inl rfl) (2 / 3) (by norm_num) (1 / 3) (1 / 3) 0
    (by norm_num) (by norm_num) (by norm_num)

theorem thirdsAc_hasContent (A : ℕ → ℕ → Prop) (hA : ∀ r m, A r m → ThirdsAdm r m) (d : ℕ) :
    HasContent (commonMinorFam thirdsAc A d) (32313 / 10000) :=
  thirds_hasContent thirdsAc_data
    (Or.inl ⟨thirds_band_2_1 thirdsAc_data, thirds_band_2_5 thirdsAc_data⟩) A hA d

theorem thirdsBc_hasContent (A : ℕ → ℕ → Prop) (hA : ∀ r m, A r m → ThirdsAdm r m) (d : ℕ) :
    HasContent (commonMinorFam thirdsBc A d) (32313 / 10000) :=
  thirds_hasContent thirdsBc_data
    (Or.inr ⟨thirds_band_1_1 thirdsBc_data, thirds_band_1_5 thirdsBc_data⟩) A hA d

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.thirdsAc_hasContent
#print axioms CatalanFrames.Thirds.thirdsBc_hasContent
