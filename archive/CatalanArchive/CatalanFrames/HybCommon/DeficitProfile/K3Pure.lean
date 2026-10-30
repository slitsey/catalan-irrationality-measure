module
public import CatalanFrames.HybCommon.DeficitProfile.Family
@[expose] public section
namespace CatalanFrames.HybCommon

lemma k3_pure (m L R Lub Rlb t0 t1 tl0 tl1 sz : ℕ) (hL : L ≤ Lub) (hR : Rlb ≤ R)
    (h0 : tl0 ≤ t0) (h1 : tl1 ≤ t1) :
    min m (((Rlb-Lub)-m) + (((Rlb-Lub)-m) - (sz - (tl0+tl1)))) ≤
      min m (((R-L)-m) + (((R-L)-m) - (sz - (t0+t1)))) := by omega

end CatalanFrames.HybCommon
