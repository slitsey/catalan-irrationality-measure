module

public import CatalanFrames.Thirds.ContentInstances

@[expose] public section

/-! # Exact finite-table content price for the thirds frames

The table geometry and admissible window are unchanged. This module avoids rounding
`Clow + Chigh` upwards to four decimal places.
-/

open CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.HybCommon

namespace CatalanFrames.Thirds

/-- Exact sum of the two finite-table class constants. -/
def thirdsSharpPrice : ℚ := 43074084803 / 13330437120

theorem Clow_add_Chigh_eq_sharpPrice : Clow + Chigh = (thirdsSharpPrice : ℝ) := by
  simp only [thirdsSharpPrice, Clow, Chigh, listInt_append, ld1, tlow, thigh, listInt,
    Piece.int, mkPiece]
  norm_num

theorem thirdsAc_hasContent_sharp (A : ℕ → ℕ → Prop)
    (hA : ∀ r m, A r m → ThirdsAdm r m) (d : ℕ) :
    HasContent (commonMinorFam thirdsAc A d) (thirdsSharpPrice : ℝ) :=
  thirds_hasContent_le thirdsAc_data (thirdsSharpPrice : ℝ)
    (le_of_eq Clow_add_Chigh_eq_sharpPrice)
    (Or.inl ⟨thirds_band_2_1 thirdsAc_data, thirds_band_2_5 thirdsAc_data⟩) A hA d

theorem thirdsBc_hasContent_sharp (A : ℕ → ℕ → Prop)
    (hA : ∀ r m, A r m → ThirdsAdm r m) (d : ℕ) :
    HasContent (commonMinorFam thirdsBc A d) (thirdsSharpPrice : ℝ) :=
  thirds_hasContent_le thirdsBc_data (thirdsSharpPrice : ℝ)
    (le_of_eq Clow_add_Chigh_eq_sharpPrice)
    (Or.inr ⟨thirds_band_1_1 thirdsBc_data, thirds_band_1_5 thirdsBc_data⟩) A hA d

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.Clow_add_Chigh_eq_sharpPrice
#print axioms CatalanFrames.Thirds.thirdsAc_hasContent_sharp
#print axioms CatalanFrames.Thirds.thirdsBc_hasContent_sharp
