module

public import CatalanFrames.LambdaMirrorHybrid.MirInst
public import CatalanFrames.HybCommon.DefAll

@[expose] public section

/-!
# Mirror: the glued deficit family (E, B, C5, C7, GK) for `mirNInst`

`mir_defHypT_all3`: for `r ≥ 16`, `m = r/8`, the deficit family `defG 3 r` (value `m` on the clean primes of
E (`p ≡ 3 mod 4` for `j = 3`, `p ≡ 1 mod 4` for `j = 1`) and on the GK band, `m - (p - r)` on
`r < p < r + m`, `L_p - m` on the C5 and C7 windows) is valid for `mirNInst` against `TfunG 3 mirNInst r`.
-/

open CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.HybCommon

namespace CatalanFrames.LambdaMirrorHybrid

theorem mir_defHypT_all3 {r : ℕ} (hr : 16 ≤ r) :
    DefHypT mirNInst r (r / 8) (TfunG 3 mirNInst r) (defG 3 r) :=
  defHypT_allG mirNInst mirNData (Or.inr rfl) hr

end CatalanFrames.LambdaMirrorHybrid
