module

public import CatalanFrames.LambdaHybrid.NV.FinalS
public import CatalanFrames.LambdaHybrid.NV.HDelta

/-!
# `nv_hyb_pair_genS` with `hΔ` discharged

The hypothesis `hΔ` of `nv_hyb_pair_genS` (the border determinant `det(W_Xᵀ W_Y)` is a unit mod `ℓ`)
follows from `hDelta_after` (closed form of Prop hDelta at `θ = 0` + `Delta_LU`), given
`1 ≤ K`, `m ≤ K`.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

variable {ℓ K : ℕ} [Fact ℓ.Prime]

theorem nv_hyb_pair_genS_auto {Fr : Frame} (D : ModData Fr ℓ K) (m s' r : ℕ) (hK : 1 ≤ K)
    (hmK : m ≤ K) (hrK : K ≤ r) (hr : r + 2 * m + (s' + 1) = ℓ)
    {x : ℚ} (hx : x ∈ S ℓ)
    (h1 : ((after r m).Full Fr x).det = 0) (h2 : ((afterTop r m).Full Fr x).det = 0) :
    (∀ (n : ℕ) (U : Matrix (Fin K) (Fin n) (ZMod ℓ)), SpansKer (WX ℓ K (after r m)) U →
        kgenR' (N2 ℓ K s') (wLast ℓ K s') (WX ℓ K (after r m)) (WY ℓ K (after r m)) U = 0) ∨
    (∀ (n : ℕ) (U : Matrix (Fin K) (Fin n) (ZMod ℓ)), SpansKer (WY ℓ K (after r m)) U →
        kgenL' (N2 ℓ K s') (wLast ℓ K s') (WX ℓ K (after r m)) (WY ℓ K (after r m)) U = 0) :=
  nv_hyb_pair_genS D m s' r hrK hr (hDelta_after K m r hK hmK hrK (by omega)) hx h1 h2

end CatalanFrames.LambdaHybrid.NV
