module
public import CatalanCore.NV.Hybrid.PairFinal
public import CatalanFrames.LambdaHybrid.NV.LamData
@[expose] public section
open Finset Matrix CatalanCore CatalanCore.Rect CatalanFrames.Lambda
namespace CatalanFrames.LambdaHybrid.NV
variable {ℓ K : ℕ} [Fact ℓ.Prime]
/-- **The WP-H7 deliverable for λ.**  `ℓ ≡ 3 (mod 4)`, `K = (ℓ+1)/4`, `0 ≤ m ≤ K-1`, `s' + 1 = K - m`. -/
theorem nv_hyb_pair_lam (hlK : ℓ + 1 = 4 * K) (m s' : ℕ) (hs : s' + 1 + m = K) {x : ℚ}
    (hx : x ∈ S ℓ) (h1 : ((after (ℓ - K - m) m).Full lamFrame x).det = 0)
    (h2 : ((afterTop (ℓ - K - m) m).Full lamFrame x).det = 0) :
    kR (gramHat (Gcols ℓ K (ndAbs ℓ s')) (WX ℓ K (after (ℓ - K - m) m))
        (WY ℓ K (after (ℓ - K - m) m))) (Fin.last s') = 0 ∨
    kL (gramHat (Gcols ℓ K (ndAbs ℓ s')) (WX ℓ K (after (ℓ - K - m) m))
        (WY ℓ K (after (ℓ - K - m) m))) (Fin.last s') = 0 :=
  nv_hyb_pair_gen (lamData hlK) m s' hs (by omega) hx h1 h2

end CatalanFrames.LambdaHybrid.NV
