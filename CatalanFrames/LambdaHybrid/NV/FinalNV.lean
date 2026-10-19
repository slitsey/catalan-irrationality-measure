module

public import CatalanFrames.LambdaHybrid.NV.FinalKS
public import CatalanCore.Star.Leonard.LpGood

/-!
# The unconditional hybrid nonvanishing

`nv_hyb_nonvanishing`: for `1 ≤ m < K ≤ r`, `r + 2m + (s'+1) = ℓ`, `K - m ≤ s'+1`, the two hybrid member
determinants `det (after r m).Full Fr x` and `det (afterTop r m).Full Fr x` cannot both vanish at
`x ∈ S ℓ`.  Route: Darboux/Leonard induction (diagonal steps + K-steps) in the `GoodF` interface.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

variable {ℓ K : ℕ} [Fact ℓ.Prime]

theorem nv_hyb_nonvanishing {Fr : Frame} (D : ModData Fr ℓ K) (m s' r : ℕ)
    (hm : 1 ≤ m) (hmK : m < K) (hrK : K ≤ r) (hr : r + 2 * m + (s' + 1) = ℓ)
    (hS : K - m ≤ s' + 1) {x : ℚ} (hx : x ∈ CatalanCore.S ℓ)
    (h1 : ((after r m).Full Fr x).det = 0) (h2 : ((afterTop r m).Full Fr x).det = 0) : False :=
  nv_hyb_nonvanishing_of_KS D m s' r hm hmK hrK hr hS
    (CatalanCore.Star.Leonard.ks_transfer_of_LpG m hm fun n' hn' hl =>
      CatalanCore.Star.Leonard.LpG_good m n' hm hn' hl) hx h1 h2

#print axioms nv_hyb_nonvanishing

end CatalanFrames.LambdaHybrid.NV
