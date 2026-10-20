module
public import CatalanFrames.HybCommon.DeficitProfile.Family
public import CatalanFrames.HybCommon.Deficit7
@[expose] public section
open Classical CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon
lemma defG_eq_dAll7 {o r : ℕ} (ho : o=1 ∨ o=3) (hr : 16≤r) (p : ℕ) :
    defG o r p=dAll7 o r p := by
  by_cases hl : LowCleanO o r (r/8) p
  · rw [defG_lc hl,dAll7_lc ho hr hl]
  by_cases h7 : WC7G o r p
  · rw [defG_c7 ho hr h7,dAll7_c7 ho hr h7]
  by_cases h5 : WC5G o r p
  · rw [defG_c5 ho hr h5,dAll7_c5 ho hr h5]
  by_cases hb : WBG r p
  · rw [defG_b ho hr hb,dAll7_b ho hr hb]
  by_cases h3 : cleanE3G o r p
  · rw [defG_e3 ho hr h3,dAll7_e3 ho hr h3]
  by_cases h1 : cleanE1G o r p
  · rw [defG_e1 ho hr h1,dAll7_e1 ho hr h1]
  rw [dAll7_zero ho hl h7 h5 hb h3 h1]
  simp [defG,hl,h7,h5,hb,h3,h1]
lemma profileDeficit_disjoint_all7 {o r : ℕ} (ho : o=1 ∨ o=3) (hr : 16≤r) (p : ℕ) :
    dAll7 o r p=0 ∨ profileDeficit o r p=0 := by
  rw [←defG_eq_dAll7 ho hr p]
  exact profileDeficit_disjoint o r p
end CatalanFrames.HybCommon
