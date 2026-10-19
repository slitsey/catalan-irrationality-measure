module

public import CatalanFrames.LambdaHybrid.NV.FinalSAuto
public import CatalanFrames.LambdaHybrid.NV.KgenMod
public import CatalanCore.Star.Leonard.KgenLUL

/-!
# The hybrid nonvanishing, modulo the generic closed form of `k^gen`

All the glue of the hybrid nonvanishing is in place: `nv_hyb_pair_genS_auto` (primal pair, `hΔ`
discharged), `kgenR'_ne_zero_of_LU` / `kgenL'_ne_zero_of_LU` (last mile `ℚ → 𝔽_ℓ`),
`kgen_LU_of_formula` / `kgenL_LU_of_formula` (`θ → 0` + `κ_S` unit).  The single missing input is the
generic closed form `hgen : kgen K m S θ = σ · κ_S / ∏(θ+c)^{e_c}` (`0 < θ < 1` rational).
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

variable {ℓ K : ℕ} [Fact ℓ.Prime]

theorem nv_hyb_nonvanishing_of_formula {Fr : Frame} (D : ModData Fr ℓ K) (m s' r : ℕ)
    (hmK : m < K) (hrK : K ≤ r) (hr : r + 2 * m + (s' + 1) = ℓ) (hS : K - m ≤ s' + 1)
    (σ : ℚ) (hσ : σ = 1 ∨ σ = -1)
    (hgen : ∀ θ : ℚ, 0 < θ → θ < 1 →
      CatalanCore.Star.kgen K m (s' + 1) θ = σ * CatalanCore.Star.Fclosed K m (s' + 1) θ)
    {x : ℚ} (hx : x ∈ CatalanCore.S ℓ)
    (h1 : ((after r m).Full Fr x).det = 0) (h2 : ((afterTop r m).Full Fr x).det = 0) : False := by
  have hl : (s' + 1) + K + 2 * m ≤ ℓ := by omega
  have hR := CatalanCore.Star.kgen_LU_of_formula (ℓ := ℓ) K m (s' + 1) hmK hS hl σ hσ hgen
  have hL := CatalanCore.Star.kgenL_LU_of_formula (ℓ := ℓ) K m (s' + 1) hmK hS hl σ hσ hgen
  obtain ⟨U, hU, hne⟩ := kgenR'_ne_zero_of_LU K m r s' hmK hrK hr hR
  obtain ⟨U', hU', hne'⟩ := kgenL'_ne_zero_of_LU K m r s' hmK hrK hr (by simpa using hL)
  rcases nv_hyb_pair_genS_auto D m s' r (by omega) hmK.le hrK hr hx h1 h2 with h | h
  · exact hne (h _ U hU)
  · exact hne' (h _ U' hU')

end CatalanFrames.LambdaHybrid.NV
