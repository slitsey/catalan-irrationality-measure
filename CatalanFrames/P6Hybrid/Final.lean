module

public import CatalanFrames.P6Hybrid.Data3
public import CatalanFrames.LambdaHybrid.NV.FinalNV

/-!
# P6 hybrid nonvanishing

For `ℓ = 6t+1` prime, `1 ≤ m`, `2m+1 ≤ t` (the band `S + K + 2m ≤ ℓ`) and `r = 3t - 2m = (ℓ-1)/2 - 2m`:
the two hybrid members `after r m` and `afterTop r m` of the `L(2,χ₋₃)` frame have no common root in
`ℤ_(ℓ)`.  No hypothesis on `det R_{X'Y'}` over `ℚ` is used.
-/

@[expose] public section

open Finset CatalanCore CatalanFrames.LambdaHybrid.NV CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

variable {ℓ t : ℕ} [Fact ℓ.Prime]

theorem p6_hyb_nonvanishing (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t) (m : ℕ) (hm : 1 ≤ m)
    (hband : 2 * m + 1 ≤ t) {x : ℚ} (hx : x ∈ S ℓ)
    (h1 : ((Rect.after (3 * t - 2 * m) m).Full p6Frame x).det = 0)
    (h2 : ((Rect.afterTop (3 * t - 2 * m) m).Full p6Frame x).det = 0) : False :=
  nv_hyb_nonvanishing_gen (p6Data3 hl ht) m (3 * t) (3 * t - 2 * m) hm (by omega) (by omega)
    (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩) hx h1 h2

#print axioms p6_hyb_nonvanishing

end CatalanFrames.P6Hybrid
