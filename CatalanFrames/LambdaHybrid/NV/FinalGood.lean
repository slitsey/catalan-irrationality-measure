module

public import CatalanFrames.LambdaHybrid.NV.FinalSLU
public import CatalanCore.Star.Leonard.GoodForm

/-!
# The hybrid nonvanishing, modulo the *good form* of `k^gen`

Same as `nv_hyb_nonvanishing_of_formula`, but the generic closed form is replaced by the weaker and
easier-to-prove statement `GoodF ℓ B (kgen K m (s'+1))`: on positive generic rationals `kgen` is an
`ℓ`-unit times an integer-exponent product of the factors `θ + c`, `1 ≤ c ≤ B < ℓ`.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

variable {ℓ K : ℕ} [Fact ℓ.Prime]

theorem nv_hyb_nonvanishing_of_good {Fr : Frame} (D : ModData Fr ℓ K) (m s' r : ℕ)
    (hmK : m < K) (hrK : K ≤ r) (hr : r + 2 * m + (s' + 1) = ℓ) (hS : K - m ≤ s' + 1)
    (B : ℕ) (hB : B < ℓ)
    (hg : CatalanCore.Star.Leonard.GoodF ℓ B (CatalanCore.Star.kgen K m (s' + 1)))
    {x : ℚ} (hx : x ∈ CatalanCore.S ℓ)
    (h1 : ((after r m).Full Fr x).det = 0) (h2 : ((afterTop r m).Full Fr x).det = 0) : False := by
  have hl : (s' + 1) + K + 2 * m ≤ ℓ := by omega
  have hR := CatalanCore.Star.Leonard.kgen_LU_of_good (ℓ := ℓ) K m (s' + 1) B hmK hS hB hg
  have hL := CatalanCore.Star.Leonard.kgenL_LU_of_good (ℓ := ℓ) K m (s' + 1) B hmK hS hl hB hg
  obtain ⟨U, hU, hne⟩ := kgenR'_ne_zero_of_LU K m r s' hmK hrK hr hR
  obtain ⟨U', hU', hne'⟩ := kgenL'_ne_zero_of_LU K m r s' hmK hrK hr (by simpa using hL)
  rcases nv_hyb_pair_genS_auto D m s' r (by omega) hmK.le hrK hr hx h1 h2 with h | h
  · exact hne (h _ U hU)
  · exact hne' (h _ U' hU')

end CatalanFrames.LambdaHybrid.NV
