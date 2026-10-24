module

public import CatalanFrames.LambdaMirrorHybrid.MirData
public import CatalanCore.NV.Hybrid.FinalNV

/-!
# Mirror hybrid nonvanishing (`λ' = G/2 + 5π²/96`, `ℓ = 4K - 3`)

`nv_hyb_nonvanishing` (frame-generic) applied to `mirData`.
-/

@[expose] public section

open CatalanFrames.LambdaHybrid.NV CatalanFrames.LambdaMirror CatalanFrames.Lambda CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaMirrorHybrid

variable {ℓ K : ℕ} [Fact ℓ.Prime]

theorem mir_hyb_nonvanishing (hlK : ℓ + 3 = 4 * K) (m s' r : ℕ)
    (hm : 1 ≤ m) (hmK : m < K) (hrK : K ≤ r) (hr : r + 2 * m + (s' + 1) = ℓ)
    (hS : K - m ≤ s' + 1) {x : ℚ} (hx : x ∈ CatalanCore.S ℓ)
    (h1 : ((after r m).Full mirFrame x).det = 0)
    (h2 : ((afterTop r m).Full mirFrame x).det = 0) : False :=
  nv_hyb_nonvanishing (mirData hlK) m s' r hm hmK hrK hr hS hx h1 h2

#print axioms mir_hyb_nonvanishing

end CatalanFrames.LambdaMirrorHybrid
